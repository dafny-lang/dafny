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
      Dafny.ISequence<Dafny.Rune> _1108___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1108___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1108___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1108___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in123 = (i).Drop(new BigInteger(2));
        i = _in123;
        goto TAIL_CALL_START;
      } else {
        _1108___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1108___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in124 = (i).Drop(BigInteger.One);
        i = _in124;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1109___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1109___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1109___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1109___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in125 = (i).Drop(BigInteger.One);
        i = _in125;
        goto TAIL_CALL_START;
      } else {
        _1109___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1109___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _1110_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1110_r);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeField(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1111_r = (f);
      if ((DCOMP.__default.reserved__fields).Contains(_1111_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1111_r);
      } else {
        return DCOMP.__default.escapeName(f);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeDtor(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1112_r = (f);
      if ((DCOMP.__default.reserved__fields).Contains(_1112_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1112_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": r#_")), _1112_r);
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
        Std.Wrappers._IOption<DAST._IResolvedType> _1113_res = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
          DAST._IType _source51 = (rs).Select(BigInteger.Zero);
          bool unmatched51 = true;
          if (unmatched51) {
            if (_source51.is_UserDefined) {
              DAST._IResolvedType _1114_resolvedType = _source51.dtor_resolved;
              unmatched51 = false;
              return DCOMP.__default.TraitTypeContainingMethod(_1114_resolvedType, _pat_let_tv134);
            }
          }
          if (unmatched51) {
            unmatched51 = false;
            return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
          }
          throw new System.Exception("unexpected control point");
        }))();
        Std.Wrappers._IOption<DAST._IResolvedType> _source52 = _1113_res;
        bool unmatched52 = true;
        if (unmatched52) {
          if (_source52.is_Some) {
            unmatched52 = false;
            return _1113_res;
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
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1115_path = _let_tmp_rhs52.dtor_path;
      Dafny.ISequence<DAST._IType> _1116_typeArgs = _let_tmp_rhs52.dtor_typeArgs;
      DAST._IResolvedTypeBase _1117_kind = _let_tmp_rhs52.dtor_kind;
      Dafny.ISequence<DAST._IAttribute> _1118_attributes = _let_tmp_rhs52.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1119_properMethods = _let_tmp_rhs52.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1120_extendedTypes = _let_tmp_rhs52.dtor_extendedTypes;
      if ((_1119_properMethods).Contains(dafnyName)) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(r);
      } else {
        return DCOMP.__default.TraitTypeContainingMethodAux(_1120_extendedTypes, dafnyName);
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
      DCOMP._IEnvironment _1121_dt__update__tmp_h0 = this;
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1122_dt__update_htypes_h0 = ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType>>)(() => {
        var _coll6 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in ((this).dtor_types).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _1123_k = (Dafny.ISequence<Dafny.Rune>)_compr_6;
          if (((this).dtor_types).Contains(_1123_k)) {
            _coll6.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>(_1123_k, (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,_1123_k)).ToOwned()));
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IType>.FromCollection(_coll6);
      }))();
      return DCOMP.Environment.create((_1121_dt__update__tmp_h0).dtor_names, _1122_dt__update_htypes_h0);
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
      BigInteger _1124_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1124_indexInEnv), ((this).dtor_names).Drop((_1124_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
      Dafny.ISequence<Dafny.Rune> _1125_modName;
      _1125_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_1125_modName);
      } else {
        Dafny.ISequence<RAST._IModDecl> _1126_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _1126_body = _out15;
        s = RAST.Mod.create_Mod(_1125_modName, _1126_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi5 = new BigInteger((body).Count);
      for (BigInteger _1127_i = BigInteger.Zero; _1127_i < _hi5; _1127_i++) {
        Dafny.ISequence<RAST._IModDecl> _1128_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source53 = (body).Select(_1127_i);
        bool unmatched53 = true;
        if (unmatched53) {
          if (_source53.is_Module) {
            DAST._IModule _1129_m = _source53.dtor_Module_a0;
            unmatched53 = false;
            RAST._IMod _1130_mm;
            RAST._IMod _out16;
            _out16 = (this).GenModule(_1129_m, containingPath);
            _1130_mm = _out16;
            _1128_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1130_mm));
          }
        }
        if (unmatched53) {
          if (_source53.is_Class) {
            DAST._IClass _1131_c = _source53.dtor_Class_a0;
            unmatched53 = false;
            Dafny.ISequence<RAST._IModDecl> _out17;
            _out17 = (this).GenClass(_1131_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1131_c).dtor_name)));
            _1128_generated = _out17;
          }
        }
        if (unmatched53) {
          if (_source53.is_Trait) {
            DAST._ITrait _1132_t = _source53.dtor_Trait_a0;
            unmatched53 = false;
            Dafny.ISequence<RAST._IModDecl> _out18;
            _out18 = (this).GenTrait(_1132_t, containingPath);
            _1128_generated = _out18;
          }
        }
        if (unmatched53) {
          if (_source53.is_Newtype) {
            DAST._INewtype _1133_n = _source53.dtor_Newtype_a0;
            unmatched53 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenNewtype(_1133_n);
            _1128_generated = _out19;
          }
        }
        if (unmatched53) {
          if (_source53.is_SynonymType) {
            DAST._ISynonymType _1134_s = _source53.dtor_SynonymType_a0;
            unmatched53 = false;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenSynonymType(_1134_s);
            _1128_generated = _out20;
          }
        }
        if (unmatched53) {
          DAST._IDatatype _1135_d = _source53.dtor_Datatype_a0;
          unmatched53 = false;
          Dafny.ISequence<RAST._IModDecl> _out21;
          _out21 = (this).GenDatatype(_1135_d);
          _1128_generated = _out21;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1128_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1136_genTpConstraint;
      _1136_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1136_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1136_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1136_genTpConstraint);
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
        for (BigInteger _1137_tpI = BigInteger.Zero; _1137_tpI < _hi6; _1137_tpI++) {
          DAST._ITypeArgDecl _1138_tp;
          _1138_tp = (@params).Select(_1137_tpI);
          DAST._IType _1139_typeArg;
          RAST._ITypeParamDecl _1140_typeParam;
          DAST._IType _out22;
          RAST._ITypeParamDecl _out23;
          (this).GenTypeParam(_1138_tp, out _out22, out _out23);
          _1139_typeArg = _out22;
          _1140_typeParam = _out23;
          RAST._IType _1141_rType;
          RAST._IType _out24;
          _out24 = (this).GenType(_1139_typeArg, DCOMP.GenTypeContext.@default());
          _1141_rType = _out24;
          typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1139_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1141_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1140_typeParam));
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
      Dafny.ISequence<DAST._IType> _1142_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1143_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1144_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1145_whereConstraints;
      Dafny.ISequence<DAST._IType> _out25;
      Dafny.ISequence<RAST._IType> _out26;
      Dafny.ISequence<RAST._ITypeParamDecl> _out27;
      Dafny.ISequence<Dafny.Rune> _out28;
      (this).GenTypeParameters((c).dtor_typeParams, out _out25, out _out26, out _out27, out _out28);
      _1142_typeParamsSeq = _out25;
      _1143_rTypeParams = _out26;
      _1144_rTypeParamsDecls = _out27;
      _1145_whereConstraints = _out28;
      Dafny.ISequence<Dafny.Rune> _1146_constrainedTypeParams;
      _1146_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1144_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1147_fields;
      _1147_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1148_fieldInits;
      _1148_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1149_fieldI = BigInteger.Zero; _1149_fieldI < _hi7; _1149_fieldI++) {
        DAST._IField _1150_field;
        _1150_field = ((c).dtor_fields).Select(_1149_fieldI);
        RAST._IType _1151_fieldType;
        RAST._IType _out29;
        _out29 = (this).GenType(((_1150_field).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
        _1151_fieldType = _out29;
        Dafny.ISequence<Dafny.Rune> _1152_fieldRustName;
        _1152_fieldRustName = DCOMP.__default.escapeName(((_1150_field).dtor_formal).dtor_name);
        _1147_fields = Dafny.Sequence<RAST._IField>.Concat(_1147_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1152_fieldRustName, _1151_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source54 = (_1150_field).dtor_defaultValue;
        bool unmatched54 = true;
        if (unmatched54) {
          if (_source54.is_Some) {
            DAST._IExpression _1153_e = _source54.dtor_value;
            unmatched54 = false;
            {
              RAST._IExpr _1154_expr;
              DCOMP._IOwnership _1155___v48;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1156___v49;
              RAST._IExpr _out30;
              DCOMP._IOwnership _out31;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
              (this).GenExpr(_1153_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
              _1154_expr = _out30;
              _1155___v48 = _out31;
              _1156___v49 = _out32;
              _1148_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1148_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1152_fieldRustName, _1154_expr)));
            }
          }
        }
        if (unmatched54) {
          unmatched54 = false;
          {
            RAST._IExpr _1157_default;
            _1157_default = RAST.__default.std__Default__default;
            if ((_1151_fieldType).IsObjectOrPointer()) {
              _1157_default = (_1151_fieldType).ToNullExpr();
            }
            _1148_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1148_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1152_fieldRustName, _1157_default)));
          }
        }
      }
      BigInteger _hi8 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1158_typeParamI = BigInteger.Zero; _1158_typeParamI < _hi8; _1158_typeParamI++) {
        DAST._IType _1159_typeArg;
        RAST._ITypeParamDecl _1160_typeParam;
        DAST._IType _out33;
        RAST._ITypeParamDecl _out34;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1158_typeParamI), out _out33, out _out34);
        _1159_typeArg = _out33;
        _1160_typeParam = _out34;
        RAST._IType _1161_rTypeArg;
        RAST._IType _out35;
        _out35 = (this).GenType(_1159_typeArg, DCOMP.GenTypeContext.@default());
        _1161_rTypeArg = _out35;
        _1147_fields = Dafny.Sequence<RAST._IField>.Concat(_1147_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1158_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1161_rTypeArg))))));
        _1148_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1148_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1158_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      Dafny.ISequence<Dafny.Rune> _1162_datatypeName;
      _1162_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IStruct _1163_struct;
      _1163_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1162_datatypeName, _1144_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1147_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1163_struct));
      Dafny.ISequence<RAST._IImplMember> _1164_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1165_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out36;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out37;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(path, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Class(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1142_typeParamsSeq, out _out36, out _out37);
      _1164_implBodyRaw = _out36;
      _1165_traitBodies = _out37;
      Dafny.ISequence<RAST._IImplMember> _1166_implBody;
      _1166_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.Type.create_SelfOwned())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel((this).allocate)).ApplyType1(RAST.Type.create_SelfOwned())).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))))), _1164_implBodyRaw);
      RAST._IImpl _1167_i;
      _1167_i = RAST.Impl.create_Impl(_1144_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1162_datatypeName), _1143_rTypeParams), _1145_whereConstraints, _1166_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1167_i)));
      RAST._IType _1168_genSelfPath;
      RAST._IType _out38;
      _out38 = DCOMP.COMP.GenPath(path);
      _1168_genSelfPath = _out38;
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1144_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"))))), RAST.Type.create_TypeApp(_1168_genSelfPath, _1143_rTypeParams), _1145_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any")))))))))));
      BigInteger _hi9 = new BigInteger(((c).dtor_superClasses).Count);
      for (BigInteger _1169_i = BigInteger.Zero; _1169_i < _hi9; _1169_i++) {
        DAST._IType _1170_superClass;
        _1170_superClass = ((c).dtor_superClasses).Select(_1169_i);
        DAST._IType _source55 = _1170_superClass;
        bool unmatched55 = true;
        if (unmatched55) {
          if (_source55.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source55.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1171_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _1172_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
              unmatched55 = false;
              {
                RAST._IType _1173_pathStr;
                RAST._IType _out39;
                _out39 = DCOMP.COMP.GenPath(_1171_traitPath);
                _1173_pathStr = _out39;
                Dafny.ISequence<RAST._IType> _1174_typeArgs;
                Dafny.ISequence<RAST._IType> _out40;
                _out40 = (this).GenTypeArgs(_1172_typeArgs, DCOMP.GenTypeContext.@default());
                _1174_typeArgs = _out40;
                Dafny.ISequence<RAST._IImplMember> _1175_body;
                _1175_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_1165_traitBodies).Contains(_1171_traitPath)) {
                  _1175_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1165_traitBodies,_1171_traitPath);
                }
                RAST._IType _1176_traitType;
                _1176_traitType = RAST.Type.create_TypeApp(_1173_pathStr, _1174_typeArgs);
                RAST._IModDecl _1177_x;
                _1177_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1144_rTypeParamsDecls, _1176_traitType, RAST.Type.create_TypeApp(_1168_genSelfPath, _1143_rTypeParams), _1145_whereConstraints, _1175_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1177_x));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1144_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_1176_traitType))), RAST.Type.create_TypeApp(_1168_genSelfPath, _1143_rTypeParams), _1145_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(_1176_traitType)))))))));
              }
            }
          }
        }
        if (unmatched55) {
          unmatched55 = false;
        }
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1178_typeParamsSeq;
      _1178_typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1179_typeParamDecls;
      _1179_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1180_typeParams;
      _1180_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _hi10 = new BigInteger(((t).dtor_typeParams).Count);
        for (BigInteger _1181_tpI = BigInteger.Zero; _1181_tpI < _hi10; _1181_tpI++) {
          DAST._ITypeArgDecl _1182_tp;
          _1182_tp = ((t).dtor_typeParams).Select(_1181_tpI);
          DAST._IType _1183_typeArg;
          RAST._ITypeParamDecl _1184_typeParamDecl;
          DAST._IType _out41;
          RAST._ITypeParamDecl _out42;
          (this).GenTypeParam(_1182_tp, out _out41, out _out42);
          _1183_typeArg = _out41;
          _1184_typeParamDecl = _out42;
          _1178_typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(_1178_typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1183_typeArg));
          _1179_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1179_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1184_typeParamDecl));
          RAST._IType _1185_typeParam;
          RAST._IType _out43;
          _out43 = (this).GenType(_1183_typeArg, DCOMP.GenTypeContext.@default());
          _1185_typeParam = _out43;
          _1180_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1180_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1185_typeParam));
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1186_fullPath;
      _1186_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1187_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1188___v54;
      Dafny.ISequence<RAST._IImplMember> _out44;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out45;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1186_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Trait(), (t).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1178_typeParamsSeq, out _out44, out _out45);
      _1187_implBody = _out44;
      _1188___v54 = _out45;
      Dafny.ISequence<RAST._IType> _1189_parents;
      _1189_parents = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi11 = new BigInteger(((t).dtor_parents).Count);
      for (BigInteger _1190_i = BigInteger.Zero; _1190_i < _hi11; _1190_i++) {
        RAST._IType _1191_tpe;
        RAST._IType _out46;
        _out46 = (this).GenType(((t).dtor_parents).Select(_1190_i), DCOMP.GenTypeContext.ForTraitParents());
        _1191_tpe = _out46;
        _1189_parents = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.Concat(_1189_parents, Dafny.Sequence<RAST._IType>.FromElements(_1191_tpe)), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply1(RAST.Type.create_DynType(_1191_tpe))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1179_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1180_typeParams), _1189_parents, _1187_implBody)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1192_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1193_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1194_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1195_whereConstraints;
      Dafny.ISequence<DAST._IType> _out47;
      Dafny.ISequence<RAST._IType> _out48;
      Dafny.ISequence<RAST._ITypeParamDecl> _out49;
      Dafny.ISequence<Dafny.Rune> _out50;
      (this).GenTypeParameters((c).dtor_typeParams, out _out47, out _out48, out _out49, out _out50);
      _1192_typeParamsSeq = _out47;
      _1193_rTypeParams = _out48;
      _1194_rTypeParamsDecls = _out49;
      _1195_whereConstraints = _out50;
      Dafny.ISequence<Dafny.Rune> _1196_constrainedTypeParams;
      _1196_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1194_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1197_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source56 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      bool unmatched56 = true;
      if (unmatched56) {
        if (_source56.is_Some) {
          RAST._IType _1198_v = _source56.dtor_value;
          unmatched56 = false;
          _1197_underlyingType = _1198_v;
        }
      }
      if (unmatched56) {
        unmatched56 = false;
        RAST._IType _out51;
        _out51 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
        _1197_underlyingType = _out51;
      }
      DAST._IType _1199_resultingType;
      _1199_resultingType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _1200_newtypeName;
      _1200_newtypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1200_newtypeName, _1194_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1197_underlyingType))))));
      RAST._IExpr _1201_fnBody;
      _1201_fnBody = RAST.Expr.create_Identifier(_1200_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source57 = (c).dtor_witnessExpr;
      bool unmatched57 = true;
      if (unmatched57) {
        if (_source57.is_Some) {
          DAST._IExpression _1202_e = _source57.dtor_value;
          unmatched57 = false;
          {
            DAST._IExpression _1203_e;
            _1203_e = ((object.Equals((c).dtor_base, _1199_resultingType)) ? (_1202_e) : (DAST.Expression.create_Convert(_1202_e, (c).dtor_base, _1199_resultingType)));
            RAST._IExpr _1204_eStr;
            DCOMP._IOwnership _1205___v55;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1206___v56;
            RAST._IExpr _out52;
            DCOMP._IOwnership _out53;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out54;
            (this).GenExpr(_1203_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out52, out _out53, out _out54);
            _1204_eStr = _out52;
            _1205___v55 = _out53;
            _1206___v56 = _out54;
            _1201_fnBody = (_1201_fnBody).Apply1(_1204_eStr);
          }
        }
      }
      if (unmatched57) {
        unmatched57 = false;
        {
          _1201_fnBody = (_1201_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1207_body;
      _1207_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1201_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source58 = (c).dtor_constraint;
      bool unmatched58 = true;
      if (unmatched58) {
        if (_source58.is_None) {
          unmatched58 = false;
        }
      }
      if (unmatched58) {
        DAST._INewtypeConstraint value8 = _source58.dtor_value;
        DAST._IFormal _1208_formal = value8.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _1209_constraintStmts = value8.dtor_constraintStmts;
        unmatched58 = false;
        RAST._IExpr _1210_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1211___v57;
        DCOMP._IEnvironment _1212_newEnv;
        RAST._IExpr _out55;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out56;
        DCOMP._IEnvironment _out57;
        (this).GenStmts(_1209_constraintStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out55, out _out56, out _out57);
        _1210_rStmts = _out55;
        _1211___v57 = _out56;
        _1212_newEnv = _out57;
        Dafny.ISequence<RAST._IFormal> _1213_rFormals;
        Dafny.ISequence<RAST._IFormal> _out58;
        _out58 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_1208_formal));
        _1213_rFormals = _out58;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1194_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1200_newtypeName), _1193_rTypeParams), _1195_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _1213_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1210_rStmts))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1194_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1200_newtypeName), _1193_rTypeParams), _1195_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1207_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1194_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1200_newtypeName), _1193_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1194_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1200_newtypeName), _1193_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1197_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1214_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1215_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1216_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1217_whereConstraints;
      Dafny.ISequence<DAST._IType> _out59;
      Dafny.ISequence<RAST._IType> _out60;
      Dafny.ISequence<RAST._ITypeParamDecl> _out61;
      Dafny.ISequence<Dafny.Rune> _out62;
      (this).GenTypeParameters((c).dtor_typeParams, out _out59, out _out60, out _out61, out _out62);
      _1214_typeParamsSeq = _out59;
      _1215_rTypeParams = _out60;
      _1216_rTypeParamsDecls = _out61;
      _1217_whereConstraints = _out62;
      Dafny.ISequence<Dafny.Rune> _1218_constrainedTypeParams;
      _1218_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1216_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<Dafny.Rune> _1219_synonymTypeName;
      _1219_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _1220_resultingType;
      RAST._IType _out63;
      _out63 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
      _1220_resultingType = _out63;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1219_synonymTypeName, _1216_rTypeParamsDecls, _1220_resultingType)));
      Std.Wrappers._IOption<DAST._IExpression> _source59 = (c).dtor_witnessExpr;
      bool unmatched59 = true;
      if (unmatched59) {
        if (_source59.is_Some) {
          DAST._IExpression _1221_e = _source59.dtor_value;
          unmatched59 = false;
          {
            RAST._IExpr _1222_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1223___v58;
            DCOMP._IEnvironment _1224_newEnv;
            RAST._IExpr _out64;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out65;
            DCOMP._IEnvironment _out66;
            (this).GenStmts((c).dtor_witnessStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out64, out _out65, out _out66);
            _1222_rStmts = _out64;
            _1223___v58 = _out65;
            _1224_newEnv = _out66;
            RAST._IExpr _1225_rExpr;
            DCOMP._IOwnership _1226___v59;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1227___v60;
            RAST._IExpr _out67;
            DCOMP._IOwnership _out68;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out69;
            (this).GenExpr(_1221_e, DCOMP.SelfInfo.create_NoSelf(), _1224_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out67, out _out68, out _out69);
            _1225_rExpr = _out67;
            _1226___v59 = _out68;
            _1227___v60 = _out69;
            Dafny.ISequence<Dafny.Rune> _1228_constantName;
            _1228_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_1228_constantName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1220_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_1222_rStmts).Then(_1225_rExpr)))))));
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
          unmatched60 = false;
          return true;
        }
      }
      if (unmatched60) {
        if (_source60.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1229_ts = _source60.dtor_Tuple_a0;
          unmatched60 = false;
          return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, bool>>((_1230_ts) => Dafny.Helpers.Quantifier<DAST._IType>((_1230_ts).UniqueElements, true, (((_forall_var_5) => {
            DAST._IType _1231_t = (DAST._IType)_forall_var_5;
            return !((_1230_ts).Contains(_1231_t)) || ((this).TypeIsEq(_1231_t));
          }))))(_1229_ts);
        }
      }
      if (unmatched60) {
        if (_source60.is_Array) {
          DAST._IType _1232_t = _source60.dtor_element;
          unmatched60 = false;
          return (this).TypeIsEq(_1232_t);
        }
      }
      if (unmatched60) {
        if (_source60.is_Seq) {
          DAST._IType _1233_t = _source60.dtor_element;
          unmatched60 = false;
          return (this).TypeIsEq(_1233_t);
        }
      }
      if (unmatched60) {
        if (_source60.is_Set) {
          DAST._IType _1234_t = _source60.dtor_element;
          unmatched60 = false;
          return (this).TypeIsEq(_1234_t);
        }
      }
      if (unmatched60) {
        if (_source60.is_Multiset) {
          DAST._IType _1235_t = _source60.dtor_element;
          unmatched60 = false;
          return (this).TypeIsEq(_1235_t);
        }
      }
      if (unmatched60) {
        if (_source60.is_Map) {
          DAST._IType _1236_k = _source60.dtor_key;
          DAST._IType _1237_v = _source60.dtor_value;
          unmatched60 = false;
          return ((this).TypeIsEq(_1236_k)) && ((this).TypeIsEq(_1237_v));
        }
      }
      if (unmatched60) {
        if (_source60.is_SetBuilder) {
          DAST._IType _1238_t = _source60.dtor_element;
          unmatched60 = false;
          return (this).TypeIsEq(_1238_t);
        }
      }
      if (unmatched60) {
        if (_source60.is_MapBuilder) {
          DAST._IType _1239_k = _source60.dtor_key;
          DAST._IType _1240_v = _source60.dtor_value;
          unmatched60 = false;
          return ((this).TypeIsEq(_1239_k)) && ((this).TypeIsEq(_1240_v));
        }
      }
      if (unmatched60) {
        if (_source60.is_Arrow) {
          unmatched60 = false;
          return false;
        }
      }
      if (unmatched60) {
        if (_source60.is_Primitive) {
          unmatched60 = false;
          return true;
        }
      }
      if (unmatched60) {
        if (_source60.is_Passthrough) {
          unmatched60 = false;
          return true;
        }
      }
      if (unmatched60) {
        if (_source60.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _1241_i = _source60.dtor_TypeArg_a0;
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
      return (!((c).dtor_isCo)) && (Dafny.Helpers.Id<Func<DAST._IDatatype, bool>>((_1242_c) => Dafny.Helpers.Quantifier<DAST._IDatatypeCtor>(((_1242_c).dtor_ctors).UniqueElements, true, (((_forall_var_6) => {
        DAST._IDatatypeCtor _1243_ctor = (DAST._IDatatypeCtor)_forall_var_6;
        return Dafny.Helpers.Quantifier<DAST._IDatatypeDtor>(((_1243_ctor).dtor_args).UniqueElements, true, (((_forall_var_7) => {
          DAST._IDatatypeDtor _1244_arg = (DAST._IDatatypeDtor)_forall_var_7;
          return !((((_1242_c).dtor_ctors).Contains(_1243_ctor)) && (((_1243_ctor).dtor_args).Contains(_1244_arg))) || ((this).TypeIsEq(((_1244_arg).dtor_formal).dtor_typ));
        })));
      }))))(c));
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1245_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1246_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1247_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1248_whereConstraints;
      Dafny.ISequence<DAST._IType> _out70;
      Dafny.ISequence<RAST._IType> _out71;
      Dafny.ISequence<RAST._ITypeParamDecl> _out72;
      Dafny.ISequence<Dafny.Rune> _out73;
      (this).GenTypeParameters((c).dtor_typeParams, out _out70, out _out71, out _out72, out _out73);
      _1245_typeParamsSeq = _out70;
      _1246_rTypeParams = _out71;
      _1247_rTypeParamsDecls = _out72;
      _1248_whereConstraints = _out73;
      Dafny.ISequence<Dafny.Rune> _1249_datatypeName;
      _1249_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1250_ctors;
      _1250_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      Dafny.ISequence<DAST._IVariance> _1251_variances;
      _1251_variances = Std.Collections.Seq.__default.Map<DAST._ITypeArgDecl, DAST._IVariance>(((System.Func<DAST._ITypeArgDecl, DAST._IVariance>)((_1252_typeParamDecl) => {
        return (_1252_typeParamDecl).dtor_variance;
      })), (c).dtor_typeParams);
      BigInteger _hi12 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1253_i = BigInteger.Zero; _1253_i < _hi12; _1253_i++) {
        DAST._IDatatypeCtor _1254_ctor;
        _1254_ctor = ((c).dtor_ctors).Select(_1253_i);
        Dafny.ISequence<RAST._IField> _1255_ctorArgs;
        _1255_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1256_isNumeric;
        _1256_isNumeric = false;
        BigInteger _hi13 = new BigInteger(((_1254_ctor).dtor_args).Count);
        for (BigInteger _1257_j = BigInteger.Zero; _1257_j < _hi13; _1257_j++) {
          DAST._IDatatypeDtor _1258_dtor;
          _1258_dtor = ((_1254_ctor).dtor_args).Select(_1257_j);
          RAST._IType _1259_formalType;
          RAST._IType _out74;
          _out74 = (this).GenType(((_1258_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
          _1259_formalType = _out74;
          Dafny.ISequence<Dafny.Rune> _1260_formalName;
          _1260_formalName = DCOMP.__default.escapeName(((_1258_dtor).dtor_formal).dtor_name);
          if (((_1257_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1260_formalName))) {
            _1256_isNumeric = true;
          }
          if ((((_1257_j).Sign != 0) && (_1256_isNumeric)) && (!(Std.Strings.__default.OfNat(_1257_j)).Equals(_1260_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1260_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1257_j)));
            _1256_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1255_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1255_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1260_formalName, RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1259_formalType))))));
          } else {
            _1255_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1255_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1260_formalName, _1259_formalType))));
          }
        }
        RAST._IFields _1261_namedFields;
        _1261_namedFields = RAST.Fields.create_NamedFields(_1255_ctorArgs);
        if (_1256_isNumeric) {
          _1261_namedFields = (_1261_namedFields).ToNamelessFields();
        }
        _1250_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1250_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1254_ctor).dtor_name), _1261_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1262_selfPath;
      _1262_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1263_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1264_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out75;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out76;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1262_selfPath, _1245_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype(_1251_variances), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1245_typeParamsSeq, out _out75, out _out76);
      _1263_implBodyRaw = _out75;
      _1264_traitBodies = _out76;
      Dafny.ISequence<RAST._IImplMember> _1265_implBody;
      _1265_implBody = _1263_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1266_emittedFields;
      _1266_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi14 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1267_i = BigInteger.Zero; _1267_i < _hi14; _1267_i++) {
        DAST._IDatatypeCtor _1268_ctor;
        _1268_ctor = ((c).dtor_ctors).Select(_1267_i);
        BigInteger _hi15 = new BigInteger(((_1268_ctor).dtor_args).Count);
        for (BigInteger _1269_j = BigInteger.Zero; _1269_j < _hi15; _1269_j++) {
          DAST._IDatatypeDtor _1270_dtor;
          _1270_dtor = ((_1268_ctor).dtor_args).Select(_1269_j);
          Dafny.ISequence<Dafny.Rune> _1271_callName;
          _1271_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1270_dtor).dtor_callName, DCOMP.__default.escapeName(((_1270_dtor).dtor_formal).dtor_name));
          if (!((_1266_emittedFields).Contains(_1271_callName))) {
            _1266_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1266_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1271_callName));
            RAST._IType _1272_formalType;
            RAST._IType _out77;
            _out77 = (this).GenType(((_1270_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
            _1272_formalType = _out77;
            Dafny.ISequence<RAST._IMatchCase> _1273_cases;
            _1273_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1274_k = BigInteger.Zero; _1274_k < _hi16; _1274_k++) {
              DAST._IDatatypeCtor _1275_ctor2;
              _1275_ctor2 = ((c).dtor_ctors).Select(_1274_k);
              Dafny.ISequence<Dafny.Rune> _1276_pattern;
              _1276_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1249_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1275_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1277_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1278_hasMatchingField;
              _1278_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1279_patternInner;
              _1279_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1280_isNumeric;
              _1280_isNumeric = false;
              BigInteger _hi17 = new BigInteger(((_1275_ctor2).dtor_args).Count);
              for (BigInteger _1281_l = BigInteger.Zero; _1281_l < _hi17; _1281_l++) {
                DAST._IDatatypeDtor _1282_dtor2;
                _1282_dtor2 = ((_1275_ctor2).dtor_args).Select(_1281_l);
                Dafny.ISequence<Dafny.Rune> _1283_patternName;
                _1283_patternName = DCOMP.__default.escapeDtor(((_1282_dtor2).dtor_formal).dtor_name);
                if (((_1281_l).Sign == 0) && ((_1283_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1280_isNumeric = true;
                }
                if (_1280_isNumeric) {
                  _1283_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1282_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1281_l)));
                }
                if (object.Equals(((_1270_dtor).dtor_formal).dtor_name, ((_1282_dtor2).dtor_formal).dtor_name)) {
                  _1278_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1283_patternName);
                }
                _1279_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1279_patternInner, _1283_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1280_isNumeric) {
                _1276_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1276_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1279_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1276_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1276_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1279_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1278_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1277_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1278_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1277_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1278_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1277_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _1284_ctorMatch;
              _1284_ctorMatch = RAST.MatchCase.create(_1276_pattern, RAST.Expr.create_RawExpr(_1277_rhs));
              _1273_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1273_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1284_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1273_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1273_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1249_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _1285_methodBody;
            _1285_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1273_cases);
            _1265_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1265_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1271_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1272_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1285_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _1286_coerceTypes;
      _1286_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1287_rCoerceTypeParams;
      _1287_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _1288_coerceArguments;
      _1288_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _1289_coerceMap;
      _1289_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _1290_rCoerceMap;
      _1290_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1291_coerceMapToArg;
      _1291_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1292_types;
        _1292_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi18 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1293_typeI = BigInteger.Zero; _1293_typeI < _hi18; _1293_typeI++) {
          DAST._ITypeArgDecl _1294_typeParam;
          _1294_typeParam = ((c).dtor_typeParams).Select(_1293_typeI);
          DAST._IType _1295_typeArg;
          RAST._ITypeParamDecl _1296_rTypeParamDecl;
          DAST._IType _out78;
          RAST._ITypeParamDecl _out79;
          (this).GenTypeParam(_1294_typeParam, out _out78, out _out79);
          _1295_typeArg = _out78;
          _1296_rTypeParamDecl = _out79;
          RAST._IType _1297_rTypeArg;
          RAST._IType _out80;
          _out80 = (this).GenType(_1295_typeArg, DCOMP.GenTypeContext.@default());
          _1297_rTypeArg = _out80;
          _1292_types = Dafny.Sequence<RAST._IType>.Concat(_1292_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1297_rTypeArg))));
          if (((_1293_typeI) < (new BigInteger((_1251_variances).Count))) && (((_1251_variances).Select(_1293_typeI)).is_Nonvariant)) {
            _1286_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1286_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1297_rTypeArg));
            goto continue0;
          }
          DAST._ITypeArgDecl _1298_coerceTypeParam;
          _1298_coerceTypeParam = Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_1294_typeParam, _pat_let9_0 => Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_pat_let9_0, _1299_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_1293_typeI)), _pat_let10_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(_pat_let10_0, _1300_dt__update_hname_h0 => DAST.TypeArgDecl.create(_1300_dt__update_hname_h0, (_1299_dt__update__tmp_h0).dtor_bounds, (_1299_dt__update__tmp_h0).dtor_variance)))));
          DAST._IType _1301_coerceTypeArg;
          RAST._ITypeParamDecl _1302_rCoerceTypeParamDecl;
          DAST._IType _out81;
          RAST._ITypeParamDecl _out82;
          (this).GenTypeParam(_1298_coerceTypeParam, out _out81, out _out82);
          _1301_coerceTypeArg = _out81;
          _1302_rCoerceTypeParamDecl = _out82;
          _1289_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_1289_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_1295_typeArg, _1301_coerceTypeArg)));
          RAST._IType _1303_rCoerceType;
          RAST._IType _out83;
          _out83 = (this).GenType(_1301_coerceTypeArg, DCOMP.GenTypeContext.@default());
          _1303_rCoerceType = _out83;
          _1290_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_1290_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_1297_rTypeArg, _1303_rCoerceType)));
          _1286_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1286_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1303_rCoerceType));
          _1287_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1287_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1302_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _1304_coerceFormal;
          _1304_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_1293_typeI));
          _1291_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_1291_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_1297_rTypeArg, _1303_rCoerceType), (RAST.Expr.create_Identifier(_1304_coerceFormal)).Clone())));
          _1288_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_1288_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1304_coerceFormal, RAST.__default.Rc(RAST.Type.create_IntersectionType(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_1297_rTypeArg), _1303_rCoerceType)), RAST.__default.StaticTrait)))));
        continue0: ;
        }
      after0: ;
        _1250_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1250_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1305_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1305_tpe);
})), _1292_types)))));
      }
      bool _1306_cIsEq;
      _1306_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_1306_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _1249_datatypeName, _1247_rTypeParamsDecls, _1250_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1247_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1249_datatypeName), _1246_rTypeParams), _1248_whereConstraints, _1265_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1307_printImplBodyCases;
      _1307_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1308_hashImplBodyCases;
      _1308_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1309_coerceImplBodyCases;
      _1309_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi19 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1310_i = BigInteger.Zero; _1310_i < _hi19; _1310_i++) {
        DAST._IDatatypeCtor _1311_ctor;
        _1311_ctor = ((c).dtor_ctors).Select(_1310_i);
        Dafny.ISequence<Dafny.Rune> _1312_ctorMatch;
        _1312_ctorMatch = DCOMP.__default.escapeName((_1311_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1313_modulePrefix;
        _1313_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1314_ctorName;
        _1314_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1313_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1311_ctor).dtor_name));
        if (((new BigInteger((_1314_ctorName).Count)) >= (new BigInteger(13))) && (((_1314_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1314_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1315_printRhs;
        _1315_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1314_ctorName), (((_1311_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1316_hashRhs;
        _1316_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        Dafny.ISequence<RAST._IAssignIdentifier> _1317_coerceRhsArgs;
        _1317_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _1318_isNumeric;
        _1318_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1319_ctorMatchInner;
        _1319_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi20 = new BigInteger(((_1311_ctor).dtor_args).Count);
        for (BigInteger _1320_j = BigInteger.Zero; _1320_j < _hi20; _1320_j++) {
          DAST._IDatatypeDtor _1321_dtor;
          _1321_dtor = ((_1311_ctor).dtor_args).Select(_1320_j);
          Dafny.ISequence<Dafny.Rune> _1322_patternName;
          _1322_patternName = DCOMP.__default.escapeField(((_1321_dtor).dtor_formal).dtor_name);
          DAST._IType _1323_formalType;
          _1323_formalType = ((_1321_dtor).dtor_formal).dtor_typ;
          if (((_1320_j).Sign == 0) && ((_1322_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1318_isNumeric = true;
          }
          if (_1318_isNumeric) {
            _1322_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1321_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1320_j)));
          }
          _1316_hashRhs = (((_1323_formalType).is_Arrow) ? ((_1316_hashRhs).Then(((RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))))) : ((_1316_hashRhs).Then(((RAST.Expr.create_Identifier(_1322_patternName)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))))));
          _1319_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1319_ctorMatchInner, _1322_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1320_j).Sign == 1) {
            _1315_printRhs = (_1315_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1315_printRhs = (_1315_printRhs).Then(RAST.Expr.create_RawExpr((((_1323_formalType).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \"<function>\")?")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1322_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))))));
          RAST._IExpr _1324_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _1325_formalTpe;
          RAST._IType _out84;
          _out84 = (this).GenType(_1323_formalType, DCOMP.GenTypeContext.@default());
          _1325_formalTpe = _out84;
          DAST._IType _1326_newFormalType;
          _1326_newFormalType = (_1323_formalType).Replace(_1289_coerceMap);
          RAST._IType _1327_newFormalTpe;
          _1327_newFormalTpe = (_1325_formalTpe).Replace(_1290_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1328_upcastConverter;
          _1328_upcastConverter = (this).UpcastConversionLambda(_1323_formalType, _1325_formalTpe, _1326_newFormalType, _1327_newFormalTpe, _1291_coerceMapToArg);
          if ((_1328_upcastConverter).is_Success) {
            RAST._IExpr _1329_coercionFunction;
            _1329_coercionFunction = (_1328_upcastConverter).dtor_value;
            _1324_coerceRhsArg = (_1329_coercionFunction).Apply1(RAST.Expr.create_Identifier(_1322_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_1320_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _1249_datatypeName));
            _1324_coerceRhsArg = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("todo!"))).Apply1(RAST.Expr.create_LiteralString((this.error).dtor_value, false, false));
          }
          _1317_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1317_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1322_patternName, _1324_coerceRhsArg)));
        }
        RAST._IExpr _1330_coerceRhs;
        _1330_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_1249_datatypeName)).MSel(DCOMP.__default.escapeName((_1311_ctor).dtor_name)), _1317_coerceRhsArgs);
        if (_1318_isNumeric) {
          _1312_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1312_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1319_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1312_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1312_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1319_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1311_ctor).dtor_hasAnyArgs) {
          _1315_printRhs = (_1315_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1315_printRhs = (_1315_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1307_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1307_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1249_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1312_ctorMatch), RAST.Expr.create_Block(_1315_printRhs))));
        _1308_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1308_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1249_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1312_ctorMatch), RAST.Expr.create_Block(_1316_hashRhs))));
        _1309_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1309_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1249_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1312_ctorMatch), RAST.Expr.create_Block(_1330_coerceRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IMatchCase> _1331_extraCases;
        _1331_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1249_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}"))));
        _1307_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1307_printImplBodyCases, _1331_extraCases);
        _1308_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1308_hashImplBodyCases, _1331_extraCases);
        _1309_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1309_coerceImplBodyCases, _1331_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1332_defaultConstrainedTypeParams;
      _1332_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1247_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1333_rTypeParamsDeclsWithEq;
      _1333_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1247_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1334_rTypeParamsDeclsWithHash;
      _1334_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1247_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1335_printImplBody;
      _1335_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1307_printImplBodyCases);
      RAST._IExpr _1336_hashImplBody;
      _1336_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1308_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1247_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1249_datatypeName), _1246_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1247_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1249_datatypeName), _1246_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1335_printImplBody))))))));
      if ((new BigInteger((_1287_rCoerceTypeParams).Count)).Sign == 1) {
        RAST._IExpr _1337_coerceImplBody;
        _1337_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _1309_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1247_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1249_datatypeName), _1246_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), _1287_rCoerceTypeParams, _1288_coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1249_datatypeName), _1246_rTypeParams)), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1249_datatypeName), _1286_coerceTypes))))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.RcNew(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.Type.create_SelfOwned())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1249_datatypeName), _1286_coerceTypes)), _1337_coerceImplBody))))))))));
      }
      if (_1306_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1333_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1249_datatypeName), _1246_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1334_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1249_datatypeName), _1246_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1336_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1338_structName;
        _1338_structName = (RAST.Expr.create_Identifier(_1249_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1339_structAssignments;
        _1339_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi21 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1340_i = BigInteger.Zero; _1340_i < _hi21; _1340_i++) {
          DAST._IDatatypeDtor _1341_dtor;
          _1341_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1340_i);
          _1339_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1339_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1341_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1342_defaultConstrainedTypeParams;
        _1342_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1247_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1343_fullType;
        _1343_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1249_datatypeName), _1246_rTypeParams);
        if (_1306_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1342_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1343_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1343_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1338_structName, _1339_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1247_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_1343_fullType), RAST.Type.create_Borrowed(_1343_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
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
        for (BigInteger _1344_i = BigInteger.Zero; _1344_i < _hi22; _1344_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1344_i))));
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
        for (BigInteger _1345_i = BigInteger.Zero; _1345_i < _hi23; _1345_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1345_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, DCOMP._IGenTypeContext genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi24 = new BigInteger((args).Count);
      for (BigInteger _1346_i = BigInteger.Zero; _1346_i < _hi24; _1346_i++) {
        RAST._IType _1347_genTp;
        RAST._IType _out85;
        _out85 = (this).GenType((args).Select(_1346_i), genTypeContext);
        _1347_genTp = _out85;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1347_genTp));
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
          DAST._IResolvedType _1348_resolved = _source61.dtor_resolved;
          unmatched61 = false;
          {
            RAST._IType _1349_t;
            RAST._IType _out86;
            _out86 = DCOMP.COMP.GenPath((_1348_resolved).dtor_path);
            _1349_t = _out86;
            Dafny.ISequence<RAST._IType> _1350_typeArgs;
            Dafny.ISequence<RAST._IType> _out87;
            _out87 = (this).GenTypeArgs((_1348_resolved).dtor_typeArgs, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let11_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let11_0, _1351_dt__update__tmp_h0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let12_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let12_0, _1352_dt__update_hforTraitParents_h0 => DCOMP.GenTypeContext.create((_1351_dt__update__tmp_h0).dtor_inBinding, (_1351_dt__update__tmp_h0).dtor_inFn, _1352_dt__update_hforTraitParents_h0))))));
            _1350_typeArgs = _out87;
            s = RAST.Type.create_TypeApp(_1349_t, _1350_typeArgs);
            DAST._IResolvedTypeBase _source62 = (_1348_resolved).dtor_kind;
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
                  if ((this).IsRcWrapped((_1348_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched62) {
              if (_source62.is_Trait) {
                unmatched62 = false;
                {
                  if (((_1348_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
                  }
                  if (!((genTypeContext).dtor_forTraitParents)) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
              }
            }
            if (unmatched62) {
              DAST._IType _1353_t = _source62.dtor_baseType;
              DAST._INewtypeRange _1354_range = _source62.dtor_range;
              bool _1355_erased = _source62.dtor_erase;
              unmatched62 = false;
              {
                if (_1355_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source63 = DCOMP.COMP.NewtypeToRustType(_1353_t, _1354_range);
                  bool unmatched63 = true;
                  if (unmatched63) {
                    if (_source63.is_Some) {
                      RAST._IType _1356_v = _source63.dtor_value;
                      unmatched63 = false;
                      s = _1356_v;
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
          Dafny.ISequence<DAST._IType> _1357_types = _source61.dtor_Tuple_a0;
          unmatched61 = false;
          {
            Dafny.ISequence<RAST._IType> _1358_args;
            _1358_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1359_i;
            _1359_i = BigInteger.Zero;
            while ((_1359_i) < (new BigInteger((_1357_types).Count))) {
              RAST._IType _1360_generated;
              RAST._IType _out88;
              _out88 = (this).GenType((_1357_types).Select(_1359_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let13_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let13_0, _1361_dt__update__tmp_h1 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let14_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let14_0, _1362_dt__update_hforTraitParents_h1 => DCOMP.GenTypeContext.create((_1361_dt__update__tmp_h1).dtor_inBinding, (_1361_dt__update__tmp_h1).dtor_inFn, _1362_dt__update_hforTraitParents_h1))))));
              _1360_generated = _out88;
              _1358_args = Dafny.Sequence<RAST._IType>.Concat(_1358_args, Dafny.Sequence<RAST._IType>.FromElements(_1360_generated));
              _1359_i = (_1359_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1357_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1358_args)) : (RAST.__default.SystemTupleType(_1358_args)));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Array) {
          DAST._IType _1363_element = _source61.dtor_element;
          BigInteger _1364_dims = _source61.dtor_dims;
          unmatched61 = false;
          {
            if ((_1364_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1365_elem;
              RAST._IType _out89;
              _out89 = (this).GenType(_1363_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let15_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let15_0, _1366_dt__update__tmp_h2 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let16_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let16_0, _1367_dt__update_hforTraitParents_h2 => DCOMP.GenTypeContext.create((_1366_dt__update__tmp_h2).dtor_inBinding, (_1366_dt__update__tmp_h2).dtor_inFn, _1367_dt__update_hforTraitParents_h2))))));
              _1365_elem = _out89;
              if ((_1364_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1365_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1368_n;
                _1368_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1364_dims));
                s = ((RAST.__default.dafny__runtime__type).MSel(_1368_n)).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1365_elem));
                s = (this).Object(s);
              }
            }
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Seq) {
          DAST._IType _1369_element = _source61.dtor_element;
          unmatched61 = false;
          {
            RAST._IType _1370_elem;
            RAST._IType _out90;
            _out90 = (this).GenType(_1369_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let17_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let17_0, _1371_dt__update__tmp_h3 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let18_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let18_0, _1372_dt__update_hforTraitParents_h3 => DCOMP.GenTypeContext.create((_1371_dt__update__tmp_h3).dtor_inBinding, (_1371_dt__update__tmp_h3).dtor_inFn, _1372_dt__update_hforTraitParents_h3))))));
            _1370_elem = _out90;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1370_elem));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Set) {
          DAST._IType _1373_element = _source61.dtor_element;
          unmatched61 = false;
          {
            RAST._IType _1374_elem;
            RAST._IType _out91;
            _out91 = (this).GenType(_1373_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let19_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let19_0, _1375_dt__update__tmp_h4 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let20_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let20_0, _1376_dt__update_hforTraitParents_h4 => DCOMP.GenTypeContext.create((_1375_dt__update__tmp_h4).dtor_inBinding, (_1375_dt__update__tmp_h4).dtor_inFn, _1376_dt__update_hforTraitParents_h4))))));
            _1374_elem = _out91;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1374_elem));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Multiset) {
          DAST._IType _1377_element = _source61.dtor_element;
          unmatched61 = false;
          {
            RAST._IType _1378_elem;
            RAST._IType _out92;
            _out92 = (this).GenType(_1377_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let21_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let21_0, _1379_dt__update__tmp_h5 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let22_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let22_0, _1380_dt__update_hforTraitParents_h5 => DCOMP.GenTypeContext.create((_1379_dt__update__tmp_h5).dtor_inBinding, (_1379_dt__update__tmp_h5).dtor_inFn, _1380_dt__update_hforTraitParents_h5))))));
            _1378_elem = _out92;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1378_elem));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Map) {
          DAST._IType _1381_key = _source61.dtor_key;
          DAST._IType _1382_value = _source61.dtor_value;
          unmatched61 = false;
          {
            RAST._IType _1383_keyType;
            RAST._IType _out93;
            _out93 = (this).GenType(_1381_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let23_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let23_0, _1384_dt__update__tmp_h6 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let24_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let24_0, _1385_dt__update_hforTraitParents_h6 => DCOMP.GenTypeContext.create((_1384_dt__update__tmp_h6).dtor_inBinding, (_1384_dt__update__tmp_h6).dtor_inFn, _1385_dt__update_hforTraitParents_h6))))));
            _1383_keyType = _out93;
            RAST._IType _1386_valueType;
            RAST._IType _out94;
            _out94 = (this).GenType(_1382_value, genTypeContext);
            _1386_valueType = _out94;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1383_keyType, _1386_valueType));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_MapBuilder) {
          DAST._IType _1387_key = _source61.dtor_key;
          DAST._IType _1388_value = _source61.dtor_value;
          unmatched61 = false;
          {
            RAST._IType _1389_keyType;
            RAST._IType _out95;
            _out95 = (this).GenType(_1387_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let25_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let25_0, _1390_dt__update__tmp_h7 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let26_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let26_0, _1391_dt__update_hforTraitParents_h7 => DCOMP.GenTypeContext.create((_1390_dt__update__tmp_h7).dtor_inBinding, (_1390_dt__update__tmp_h7).dtor_inFn, _1391_dt__update_hforTraitParents_h7))))));
            _1389_keyType = _out95;
            RAST._IType _1392_valueType;
            RAST._IType _out96;
            _out96 = (this).GenType(_1388_value, genTypeContext);
            _1392_valueType = _out96;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1389_keyType, _1392_valueType));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_SetBuilder) {
          DAST._IType _1393_elem = _source61.dtor_element;
          unmatched61 = false;
          {
            RAST._IType _1394_elemType;
            RAST._IType _out97;
            _out97 = (this).GenType(_1393_elem, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let27_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let27_0, _1395_dt__update__tmp_h8 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let28_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let28_0, _1396_dt__update_hforTraitParents_h8 => DCOMP.GenTypeContext.create((_1395_dt__update__tmp_h8).dtor_inBinding, (_1395_dt__update__tmp_h8).dtor_inFn, _1396_dt__update_hforTraitParents_h8))))));
            _1394_elemType = _out97;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1394_elemType));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1397_args = _source61.dtor_args;
          DAST._IType _1398_result = _source61.dtor_result;
          unmatched61 = false;
          {
            Dafny.ISequence<RAST._IType> _1399_argTypes;
            _1399_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1400_i;
            _1400_i = BigInteger.Zero;
            while ((_1400_i) < (new BigInteger((_1397_args).Count))) {
              RAST._IType _1401_generated;
              RAST._IType _out98;
              _out98 = (this).GenType((_1397_args).Select(_1400_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let29_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let29_0, _1402_dt__update__tmp_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let30_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let30_0, _1403_dt__update_hforTraitParents_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(true, _pat_let31_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let31_0, _1404_dt__update_hinFn_h0 => DCOMP.GenTypeContext.create((_1402_dt__update__tmp_h9).dtor_inBinding, _1404_dt__update_hinFn_h0, _1403_dt__update_hforTraitParents_h9))))))));
              _1401_generated = _out98;
              _1399_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1399_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1401_generated)));
              _1400_i = (_1400_i) + (BigInteger.One);
            }
            RAST._IType _1405_resultType;
            RAST._IType _out99;
            _out99 = (this).GenType(_1398_result, DCOMP.GenTypeContext.create(((genTypeContext).dtor_inFn) || ((genTypeContext).dtor_inBinding), false, false));
            _1405_resultType = _out99;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1399_argTypes, _1405_resultType)));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source61.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1406_name = _h90;
          unmatched61 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1406_name));
        }
      }
      if (unmatched61) {
        if (_source61.is_Primitive) {
          DAST._IPrimitive _1407_p = _source61.dtor_Primitive_a0;
          unmatched61 = false;
          {
            DAST._IPrimitive _source64 = _1407_p;
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
        Dafny.ISequence<Dafny.Rune> _1408_v = _source61.dtor_Passthrough_a0;
        unmatched61 = false;
        s = RAST.__default.RawType(_1408_v);
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
      for (BigInteger _1409_i = BigInteger.Zero; _1409_i < _hi25; _1409_i++) {
        DAST._IMethod _source65 = (body).Select(_1409_i);
        bool unmatched65 = true;
        if (unmatched65) {
          DAST._IMethod _1410_m = _source65;
          unmatched65 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source66 = (_1410_m).dtor_overridingPath;
            bool unmatched66 = true;
            if (unmatched66) {
              if (_source66.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1411_p = _source66.dtor_value;
                unmatched66 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1412_existing;
                  _1412_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1411_p)) {
                    _1412_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1411_p);
                  }
                  if (((new BigInteger(((_1410_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _1413_genMethod;
                  RAST._IImplMember _out100;
                  _out100 = (this).GenMethod(_1410_m, true, enclosingType, enclosingTypeParams);
                  _1413_genMethod = _out100;
                  _1412_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1412_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1413_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1411_p, _1412_existing)));
                }
              }
            }
            if (unmatched66) {
              unmatched66 = false;
              {
                RAST._IImplMember _1414_generated;
                RAST._IImplMember _out101;
                _out101 = (this).GenMethod(_1410_m, forTrait, enclosingType, enclosingTypeParams);
                _1414_generated = _out101;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1414_generated));
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
      for (BigInteger _1415_i = BigInteger.Zero; _1415_i < _hi26; _1415_i++) {
        DAST._IFormal _1416_param;
        _1416_param = (@params).Select(_1415_i);
        RAST._IType _1417_paramType;
        RAST._IType _out102;
        _out102 = (this).GenType((_1416_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _1417_paramType = _out102;
        if ((!((_1417_paramType).CanReadWithoutClone())) && (!((_1416_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1417_paramType = RAST.Type.create_Borrowed(_1417_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_1416_param).dtor_name), _1417_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1418_params;
      Dafny.ISequence<RAST._IFormal> _out103;
      _out103 = (this).GenParams((m).dtor_params);
      _1418_params = _out103;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1419_paramNames;
      _1419_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1420_paramTypes;
      _1420_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi27 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1421_paramI = BigInteger.Zero; _1421_paramI < _hi27; _1421_paramI++) {
        DAST._IFormal _1422_dafny__formal;
        _1422_dafny__formal = ((m).dtor_params).Select(_1421_paramI);
        RAST._IFormal _1423_formal;
        _1423_formal = (_1418_params).Select(_1421_paramI);
        Dafny.ISequence<Dafny.Rune> _1424_name;
        _1424_name = (_1423_formal).dtor_name;
        _1419_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1419_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1424_name));
        _1420_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1420_paramTypes, _1424_name, (_1423_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1425_fnName;
      _1425_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _1426_selfIdent;
      _1426_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1427_selfId;
        _1427_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((m).dtor_outVarsAreUninitFieldsToAssign) {
          _1427_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv137 = enclosingTypeParams;
        var _pat_let_tv138 = enclosingType;
        DAST._IType _1428_instanceType;
        _1428_instanceType = ((System.Func<DAST._IType>)(() => {
          DAST._IType _source67 = enclosingType;
          bool unmatched67 = true;
          if (unmatched67) {
            if (_source67.is_UserDefined) {
              DAST._IResolvedType _1429_r = _source67.dtor_resolved;
              unmatched67 = false;
              return DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_1429_r, _pat_let32_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let32_0, _1430_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv137, _pat_let33_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let33_0, _1431_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_1430_dt__update__tmp_h0).dtor_path, _1431_dt__update_htypeArgs_h0, (_1430_dt__update__tmp_h0).dtor_kind, (_1430_dt__update__tmp_h0).dtor_attributes, (_1430_dt__update__tmp_h0).dtor_properMethods, (_1430_dt__update__tmp_h0).dtor_extendedTypes))))));
            }
          }
          if (unmatched67) {
            unmatched67 = false;
            return _pat_let_tv138;
          }
          throw new System.Exception("unexpected control point");
        }))();
        if (forTrait) {
          RAST._IFormal _1432_selfFormal;
          _1432_selfFormal = (((m).dtor_wasFunction) ? (RAST.Formal.selfBorrowed) : (RAST.Formal.selfBorrowedMut));
          _1418_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1432_selfFormal), _1418_params);
        } else {
          RAST._IType _1433_tpe;
          RAST._IType _out104;
          _out104 = (this).GenType(_1428_instanceType, DCOMP.GenTypeContext.@default());
          _1433_tpe = _out104;
          if ((_1427_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            _1433_tpe = RAST.Type.create_Borrowed(_1433_tpe);
          } else if ((_1427_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_1433_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _1433_tpe = RAST.__default.SelfBorrowed;
              } else {
                _1433_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              _1433_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.Type.create_SelfOwned()));
            }
          }
          _1418_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1427_selfId, _1433_tpe)), _1418_params);
        }
        _1426_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_1427_selfId, _1428_instanceType);
      }
      Dafny.ISequence<RAST._IType> _1434_retTypeArgs;
      _1434_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1435_typeI;
      _1435_typeI = BigInteger.Zero;
      while ((_1435_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1436_typeExpr;
        RAST._IType _out105;
        _out105 = (this).GenType(((m).dtor_outTypes).Select(_1435_typeI), DCOMP.GenTypeContext.@default());
        _1436_typeExpr = _out105;
        _1434_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1434_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1436_typeExpr));
        _1435_typeI = (_1435_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1437_visibility;
      _1437_visibility = ((forTrait) ? (RAST.Visibility.create_PRIV()) : (RAST.Visibility.create_PUB()));
      Dafny.ISequence<DAST._ITypeArgDecl> _1438_typeParamsFiltered;
      _1438_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi28 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1439_typeParamI = BigInteger.Zero; _1439_typeParamI < _hi28; _1439_typeParamI++) {
        DAST._ITypeArgDecl _1440_typeParam;
        _1440_typeParam = ((m).dtor_typeParams).Select(_1439_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1440_typeParam).dtor_name)))) {
          _1438_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1438_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1440_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1441_typeParams;
      _1441_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1438_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi29 = new BigInteger((_1438_typeParamsFiltered).Count);
        for (BigInteger _1442_i = BigInteger.Zero; _1442_i < _hi29; _1442_i++) {
          DAST._IType _1443_typeArg;
          RAST._ITypeParamDecl _1444_rTypeParamDecl;
          DAST._IType _out106;
          RAST._ITypeParamDecl _out107;
          (this).GenTypeParam((_1438_typeParamsFiltered).Select(_1442_i), out _out106, out _out107);
          _1443_typeArg = _out106;
          _1444_rTypeParamDecl = _out107;
          var _pat_let_tv139 = _1444_rTypeParamDecl;
          _1444_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1444_rTypeParamDecl, _pat_let34_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let34_0, _1445_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Dafny.Sequence<RAST._IType>.Concat((_pat_let_tv139).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default")))), _pat_let35_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let35_0, _1446_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1445_dt__update__tmp_h1).dtor_content, _1446_dt__update_hconstraints_h0)))));
          _1441_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1441_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1444_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1447_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1448_env = DCOMP.Environment.Default();
      RAST._IExpr _1449_preBody;
      _1449_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1450_preAssignNames;
      _1450_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1451_preAssignTypes;
      _1451_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        RAST._IExpr _1452_earlyReturn;
        _1452_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source68 = (m).dtor_outVars;
        bool unmatched68 = true;
        if (unmatched68) {
          if (_source68.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1453_outVars = _source68.dtor_value;
            unmatched68 = false;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1452_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(Dafny.Sequence<RAST._IExpr>.FromElements())));
                BigInteger _hi30 = new BigInteger((_1453_outVars).Count);
                for (BigInteger _1454_outI = BigInteger.Zero; _1454_outI < _hi30; _1454_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1455_outVar;
                  _1455_outVar = (_1453_outVars).Select(_1454_outI);
                  Dafny.ISequence<Dafny.Rune> _1456_outName;
                  _1456_outName = DCOMP.__default.escapeName((_1455_outVar));
                  Dafny.ISequence<Dafny.Rune> _1457_tracker__name;
                  _1457_tracker__name = DCOMP.__default.AddAssignedPrefix(_1456_outName);
                  _1450_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1450_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1457_tracker__name));
                  _1451_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1451_preAssignTypes, _1457_tracker__name, RAST.Type.create_Bool());
                  _1449_preBody = (_1449_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1457_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<RAST._IExpr> _1458_tupleArgs;
                _1458_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
                BigInteger _hi31 = new BigInteger((_1453_outVars).Count);
                for (BigInteger _1459_outI = BigInteger.Zero; _1459_outI < _hi31; _1459_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1460_outVar;
                  _1460_outVar = (_1453_outVars).Select(_1459_outI);
                  RAST._IType _1461_outType;
                  RAST._IType _out108;
                  _out108 = (this).GenType(((m).dtor_outTypes).Select(_1459_outI), DCOMP.GenTypeContext.@default());
                  _1461_outType = _out108;
                  Dafny.ISequence<Dafny.Rune> _1462_outName;
                  _1462_outName = DCOMP.__default.escapeName((_1460_outVar));
                  _1419_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1419_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1462_outName));
                  RAST._IType _1463_outMaybeType;
                  _1463_outMaybeType = (((_1461_outType).CanReadWithoutClone()) ? (_1461_outType) : (RAST.__default.MaybePlaceboType(_1461_outType)));
                  _1420_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1420_paramTypes, _1462_outName, _1463_outMaybeType);
                  RAST._IExpr _1464_outVarReturn;
                  DCOMP._IOwnership _1465___v69;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1466___v70;
                  RAST._IExpr _out109;
                  DCOMP._IOwnership _out110;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out111;
                  (this).GenExpr(DAST.Expression.create_Ident((_1460_outVar)), DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1462_outName), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>, RAST._IType>(_1462_outName, _1463_outMaybeType))), DCOMP.Ownership.create_OwnershipOwned(), out _out109, out _out110, out _out111);
                  _1464_outVarReturn = _out109;
                  _1465___v69 = _out110;
                  _1466___v70 = _out111;
                  _1458_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1458_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1464_outVarReturn));
                }
                if ((new BigInteger((_1458_tupleArgs).Count)) == (BigInteger.One)) {
                  _1452_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1458_tupleArgs).Select(BigInteger.Zero)));
                } else {
                  _1452_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1458_tupleArgs)));
                }
              }
            }
          }
        }
        if (unmatched68) {
          unmatched68 = false;
        }
        _1448_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1450_preAssignNames, _1419_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1451_preAssignTypes, _1420_paramTypes));
        RAST._IExpr _1467_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1468___v71;
        DCOMP._IEnvironment _1469___v72;
        RAST._IExpr _out112;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out113;
        DCOMP._IEnvironment _out114;
        (this).GenStmts((m).dtor_body, _1426_selfIdent, _1448_env, true, _1452_earlyReturn, out _out112, out _out113, out _out114);
        _1467_body = _out112;
        _1468___v71 = _out113;
        _1469___v72 = _out114;
        _1447_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1449_preBody).Then(_1467_body));
      } else {
        _1448_env = DCOMP.Environment.create(_1419_paramNames, _1420_paramTypes);
        _1447_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1437_visibility, RAST.Fn.create(_1425_fnName, _1441_typeParams, _1418_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1434_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1434_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1434_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1447_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1470_declarations;
      _1470_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1471_i;
      _1471_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1472_stmts;
      _1472_stmts = stmts;
      while ((_1471_i) < (new BigInteger((_1472_stmts).Count))) {
        DAST._IStatement _1473_stmt;
        _1473_stmt = (_1472_stmts).Select(_1471_i);
        DAST._IStatement _source69 = _1473_stmt;
        bool unmatched69 = true;
        if (unmatched69) {
          if (_source69.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1474_name = _source69.dtor_name;
            DAST._IType _1475_optType = _source69.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source69.dtor_maybeValue;
            if (maybeValue0.is_None) {
              unmatched69 = false;
              if (((_1471_i) + (BigInteger.One)) < (new BigInteger((_1472_stmts).Count))) {
                DAST._IStatement _source70 = (_1472_stmts).Select((_1471_i) + (BigInteger.One));
                bool unmatched70 = true;
                if (unmatched70) {
                  if (_source70.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source70.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> ident0 = lhs0.dtor_ident;
                      Dafny.ISequence<Dafny.Rune> _1476_name2 = ident0;
                      DAST._IExpression _1477_rhs = _source70.dtor_value;
                      unmatched70 = false;
                      if (object.Equals(_1476_name2, _1474_name)) {
                        _1472_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1472_stmts).Subsequence(BigInteger.Zero, _1471_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1474_name, _1475_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1477_rhs)))), (_1472_stmts).Drop((_1471_i) + (new BigInteger(2))));
                        _1473_stmt = (_1472_stmts).Select(_1471_i);
                      }
                    }
                  }
                }
                if (unmatched70) {
                  unmatched70 = false;
                }
              }
            }
          }
        }
        if (unmatched69) {
          unmatched69 = false;
        }
        RAST._IExpr _1478_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1479_recIdents;
        DCOMP._IEnvironment _1480_newEnv2;
        RAST._IExpr _out115;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
        DCOMP._IEnvironment _out117;
        (this).GenStmt(_1473_stmt, selfIdent, newEnv, (isLast) && ((_1471_i) == ((new BigInteger((_1472_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out115, out _out116, out _out117);
        _1478_stmtExpr = _out115;
        _1479_recIdents = _out116;
        _1480_newEnv2 = _out117;
        newEnv = _1480_newEnv2;
        DAST._IStatement _source71 = _1473_stmt;
        bool unmatched71 = true;
        if (unmatched71) {
          if (_source71.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1481_name = _source71.dtor_name;
            unmatched71 = false;
            {
              _1470_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1470_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_1481_name)));
            }
          }
        }
        if (unmatched71) {
          unmatched71 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1479_recIdents, _1470_declarations));
        generated = (generated).Then(_1478_stmtExpr);
        _1471_i = (_1471_i) + (BigInteger.One);
        if ((_1478_stmtExpr).is_Return) {
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
          Dafny.ISequence<Dafny.Rune> _1482_id = ident1;
          unmatched72 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1483_idRust;
            _1483_idRust = DCOMP.__default.escapeName(_1482_id);
            if (((env).IsBorrowed(_1483_idRust)) || ((env).IsBorrowedMut(_1483_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1483_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1483_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1483_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched72) {
        if (_source72.is_Select) {
          DAST._IExpression _1484_on = _source72.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1485_field = _source72.dtor_field;
          unmatched72 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1486_fieldName;
            _1486_fieldName = DCOMP.__default.escapeName(_1485_field);
            RAST._IExpr _1487_onExpr;
            DCOMP._IOwnership _1488_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1489_recIdents;
            RAST._IExpr _out118;
            DCOMP._IOwnership _out119;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out120;
            (this).GenExpr(_1484_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out118, out _out119, out _out120);
            _1487_onExpr = _out118;
            _1488_onOwned = _out119;
            _1489_recIdents = _out120;
            RAST._IExpr _source73 = _1487_onExpr;
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
                      disjunctiveMatch11 = true;
                    }
                  }
                }
              }
              if (disjunctiveMatch11) {
                unmatched73 = false;
                Dafny.ISequence<Dafny.Rune> _1490_isAssignedVar;
                _1490_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1486_fieldName);
                if (((newEnv).dtor_names).Contains(_1490_isAssignedVar)) {
                  generated = ((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1486_fieldName), RAST.Expr.create_Identifier(_1490_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1490_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _1490_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _1486_fieldName, rhs);
                }
              }
            }
            if (unmatched73) {
              unmatched73 = false;
              if (!object.Equals(_1487_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _1487_onExpr = ((this).modify__macro).Apply1(_1487_onExpr);
              }
              generated = RAST.__default.AssignMember(_1487_onExpr, _1486_fieldName, rhs);
            }
            readIdents = _1489_recIdents;
            needsIIFE = false;
          }
        }
      }
      if (unmatched72) {
        DAST._IExpression _1491_on = _source72.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1492_indices = _source72.dtor_indices;
        unmatched72 = false;
        {
          RAST._IExpr _1493_onExpr;
          DCOMP._IOwnership _1494_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1495_recIdents;
          RAST._IExpr _out121;
          DCOMP._IOwnership _out122;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out123;
          (this).GenExpr(_1491_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out121, out _out122, out _out123);
          _1493_onExpr = _out121;
          _1494_onOwned = _out122;
          _1495_recIdents = _out123;
          readIdents = _1495_recIdents;
          _1493_onExpr = ((this).modify__macro).Apply1(_1493_onExpr);
          RAST._IExpr _1496_r;
          _1496_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1497_indicesExpr;
          _1497_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi32 = new BigInteger((_1492_indices).Count);
          for (BigInteger _1498_i = BigInteger.Zero; _1498_i < _hi32; _1498_i++) {
            RAST._IExpr _1499_idx;
            DCOMP._IOwnership _1500___v81;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1501_recIdentsIdx;
            RAST._IExpr _out124;
            DCOMP._IOwnership _out125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
            (this).GenExpr((_1492_indices).Select(_1498_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out124, out _out125, out _out126);
            _1499_idx = _out124;
            _1500___v81 = _out125;
            _1501_recIdentsIdx = _out126;
            Dafny.ISequence<Dafny.Rune> _1502_varName;
            _1502_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1498_i));
            _1497_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1497_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1502_varName)));
            _1496_r = (_1496_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1502_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<usize as ::dafny_runtime::NumCast>::from("), (_1499_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"))))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1501_recIdentsIdx);
          }
          if ((new BigInteger((_1492_indices).Count)) > (BigInteger.One)) {
            _1493_onExpr = (_1493_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1503_rhs;
          _1503_rhs = rhs;
          var _pat_let_tv140 = env;
          if (((_1493_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1493_onExpr).LhsIdentifierName(), _pat_let36_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let36_0, _1504_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv140).GetType(_1504_name), _pat_let37_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let37_0, _1505_tpe => ((_1505_tpe).is_Some) && (((_1505_tpe).dtor_value).IsUninitArray())))))))) {
            _1503_rhs = RAST.__default.MaybeUninitNew(_1503_rhs);
          }
          generated = (_1496_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1493_onExpr, _1497_indicesExpr)), _1503_rhs));
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
          Dafny.ISequence<DAST._IFormal> _1506_fields = _source74.dtor_fields;
          unmatched74 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi33 = new BigInteger((_1506_fields).Count);
            for (BigInteger _1507_i = BigInteger.Zero; _1507_i < _hi33; _1507_i++) {
              DAST._IFormal _1508_field;
              _1508_field = (_1506_fields).Select(_1507_i);
              Dafny.ISequence<Dafny.Rune> _1509_fieldName;
              _1509_fieldName = DCOMP.__default.escapeName((_1508_field).dtor_name);
              RAST._IType _1510_fieldTyp;
              RAST._IType _out127;
              _out127 = (this).GenType((_1508_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _1510_fieldTyp = _out127;
              Dafny.ISequence<Dafny.Rune> _1511_isAssignedVar;
              _1511_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1509_fieldName);
              if (((newEnv).dtor_names).Contains(_1511_isAssignedVar)) {
                RAST._IExpr _1512_rhs;
                DCOMP._IOwnership _1513___v82;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1514___v83;
                RAST._IExpr _out128;
                DCOMP._IOwnership _out129;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out130;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1508_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out128, out _out129, out _out130);
                _1512_rhs = _out128;
                _1513___v82 = _out129;
                _1514___v83 = _out130;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1511_isAssignedVar));
                generated = (generated).Then(((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1509_fieldName), RAST.Expr.create_Identifier(_1511_isAssignedVar), _1512_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1511_isAssignedVar);
              }
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1515_name = _source74.dtor_name;
          DAST._IType _1516_typ = _source74.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source74.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1517_expression = maybeValue1.dtor_value;
            unmatched74 = false;
            {
              RAST._IType _1518_tpe;
              RAST._IType _out131;
              _out131 = (this).GenType(_1516_typ, DCOMP.GenTypeContext.InBinding());
              _1518_tpe = _out131;
              Dafny.ISequence<Dafny.Rune> _1519_varName;
              _1519_varName = DCOMP.__default.escapeName(_1515_name);
              bool _1520_hasCopySemantics;
              _1520_hasCopySemantics = (_1518_tpe).CanReadWithoutClone();
              if (((_1517_expression).is_InitializationValue) && (!(_1520_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1519_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).ApplyType1(_1518_tpe)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1519_varName, RAST.__default.MaybePlaceboType(_1518_tpe));
              } else {
                RAST._IExpr _1521_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1522_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1517_expression).is_InitializationValue) && ((_1518_tpe).IsObjectOrPointer())) {
                  _1521_expr = (_1518_tpe).ToNullExpr();
                  _1522_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1523_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out132;
                  DCOMP._IOwnership _out133;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out134;
                  (this).GenExpr(_1517_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out132, out _out133, out _out134);
                  _1521_expr = _out132;
                  _1523_exprOwnership = _out133;
                  _1522_recIdents = _out134;
                }
                readIdents = _1522_recIdents;
                _1518_tpe = (((_1517_expression).is_NewUninitArray) ? ((_1518_tpe).TypeAtInitialization()) : (_1518_tpe));
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_1515_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1518_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1521_expr));
                newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_1515_name), _1518_tpe);
              }
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1524_name = _source74.dtor_name;
          DAST._IType _1525_typ = _source74.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source74.dtor_maybeValue;
          if (maybeValue2.is_None) {
            unmatched74 = false;
            {
              DAST._IStatement _1526_newStmt;
              _1526_newStmt = DAST.Statement.create_DeclareVar(_1524_name, _1525_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1525_typ)));
              RAST._IExpr _out135;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out136;
              DCOMP._IEnvironment _out137;
              (this).GenStmt(_1526_newStmt, selfIdent, env, isLast, earlyReturn, out _out135, out _out136, out _out137);
              generated = _out135;
              readIdents = _out136;
              newEnv = _out137;
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Assign) {
          DAST._IAssignLhs _1527_lhs = _source74.dtor_lhs;
          DAST._IExpression _1528_expression = _source74.dtor_value;
          unmatched74 = false;
          {
            RAST._IExpr _1529_exprGen;
            DCOMP._IOwnership _1530___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1531_exprIdents;
            RAST._IExpr _out138;
            DCOMP._IOwnership _out139;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out140;
            (this).GenExpr(_1528_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out138, out _out139, out _out140);
            _1529_exprGen = _out138;
            _1530___v84 = _out139;
            _1531_exprIdents = _out140;
            if ((_1527_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1532_rustId;
              _1532_rustId = DCOMP.__default.escapeName(((_1527_lhs).dtor_ident));
              Std.Wrappers._IOption<RAST._IType> _1533_tpe;
              _1533_tpe = (env).GetType(_1532_rustId);
              if (((_1533_tpe).is_Some) && ((((_1533_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1529_exprGen = RAST.__default.MaybePlacebo(_1529_exprGen);
              }
            }
            RAST._IExpr _1534_lhsGen;
            bool _1535_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1536_recIdents;
            DCOMP._IEnvironment _1537_resEnv;
            RAST._IExpr _out141;
            bool _out142;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out143;
            DCOMP._IEnvironment _out144;
            (this).GenAssignLhs(_1527_lhs, _1529_exprGen, selfIdent, env, out _out141, out _out142, out _out143, out _out144);
            _1534_lhsGen = _out141;
            _1535_needsIIFE = _out142;
            _1536_recIdents = _out143;
            _1537_resEnv = _out144;
            generated = _1534_lhsGen;
            newEnv = _1537_resEnv;
            if (_1535_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1536_recIdents, _1531_exprIdents);
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_If) {
          DAST._IExpression _1538_cond = _source74.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1539_thnDafny = _source74.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1540_elsDafny = _source74.dtor_els;
          unmatched74 = false;
          {
            RAST._IExpr _1541_cond;
            DCOMP._IOwnership _1542___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1543_recIdents;
            RAST._IExpr _out145;
            DCOMP._IOwnership _out146;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out147;
            (this).GenExpr(_1538_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out145, out _out146, out _out147);
            _1541_cond = _out145;
            _1542___v85 = _out146;
            _1543_recIdents = _out147;
            Dafny.ISequence<Dafny.Rune> _1544_condString;
            _1544_condString = (_1541_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1543_recIdents;
            RAST._IExpr _1545_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1546_thnIdents;
            DCOMP._IEnvironment _1547_thnEnv;
            RAST._IExpr _out148;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out149;
            DCOMP._IEnvironment _out150;
            (this).GenStmts(_1539_thnDafny, selfIdent, env, isLast, earlyReturn, out _out148, out _out149, out _out150);
            _1545_thn = _out148;
            _1546_thnIdents = _out149;
            _1547_thnEnv = _out150;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1546_thnIdents);
            RAST._IExpr _1548_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1549_elsIdents;
            DCOMP._IEnvironment _1550_elsEnv;
            RAST._IExpr _out151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out152;
            DCOMP._IEnvironment _out153;
            (this).GenStmts(_1540_elsDafny, selfIdent, env, isLast, earlyReturn, out _out151, out _out152, out _out153);
            _1548_els = _out151;
            _1549_elsIdents = _out152;
            _1550_elsEnv = _out153;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1549_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1541_cond, _1545_thn, _1548_els);
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1551_lbl = _source74.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1552_body = _source74.dtor_body;
          unmatched74 = false;
          {
            RAST._IExpr _1553_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1554_bodyIdents;
            DCOMP._IEnvironment _1555_env2;
            RAST._IExpr _out154;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out155;
            DCOMP._IEnvironment _out156;
            (this).GenStmts(_1552_body, selfIdent, env, isLast, earlyReturn, out _out154, out _out155, out _out156);
            _1553_body = _out154;
            _1554_bodyIdents = _out155;
            _1555_env2 = _out156;
            readIdents = _1554_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1551_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1553_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_While) {
          DAST._IExpression _1556_cond = _source74.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1557_body = _source74.dtor_body;
          unmatched74 = false;
          {
            RAST._IExpr _1558_cond;
            DCOMP._IOwnership _1559___v86;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1560_recIdents;
            RAST._IExpr _out157;
            DCOMP._IOwnership _out158;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out159;
            (this).GenExpr(_1556_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out157, out _out158, out _out159);
            _1558_cond = _out157;
            _1559___v86 = _out158;
            _1560_recIdents = _out159;
            readIdents = _1560_recIdents;
            RAST._IExpr _1561_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1562_bodyIdents;
            DCOMP._IEnvironment _1563_bodyEnv;
            RAST._IExpr _out160;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out161;
            DCOMP._IEnvironment _out162;
            (this).GenStmts(_1557_body, selfIdent, env, false, earlyReturn, out _out160, out _out161, out _out162);
            _1561_bodyExpr = _out160;
            _1562_bodyIdents = _out161;
            _1563_bodyEnv = _out162;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1562_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1558_cond), _1561_bodyExpr);
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1564_boundName = _source74.dtor_boundName;
          DAST._IType _1565_boundType = _source74.dtor_boundType;
          DAST._IExpression _1566_overExpr = _source74.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1567_body = _source74.dtor_body;
          unmatched74 = false;
          {
            RAST._IExpr _1568_over;
            DCOMP._IOwnership _1569___v87;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1570_recIdents;
            RAST._IExpr _out163;
            DCOMP._IOwnership _out164;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out165;
            (this).GenExpr(_1566_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out163, out _out164, out _out165);
            _1568_over = _out163;
            _1569___v87 = _out164;
            _1570_recIdents = _out165;
            if (((_1566_overExpr).is_MapBoundedPool) || ((_1566_overExpr).is_SetBoundedPool)) {
              _1568_over = ((_1568_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1571_boundTpe;
            RAST._IType _out166;
            _out166 = (this).GenType(_1565_boundType, DCOMP.GenTypeContext.@default());
            _1571_boundTpe = _out166;
            readIdents = _1570_recIdents;
            Dafny.ISequence<Dafny.Rune> _1572_boundRName;
            _1572_boundRName = DCOMP.__default.escapeName(_1564_boundName);
            RAST._IExpr _1573_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1574_bodyIdents;
            DCOMP._IEnvironment _1575_bodyEnv;
            RAST._IExpr _out167;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out168;
            DCOMP._IEnvironment _out169;
            (this).GenStmts(_1567_body, selfIdent, (env).AddAssigned(_1572_boundRName, _1571_boundTpe), false, earlyReturn, out _out167, out _out168, out _out169);
            _1573_bodyExpr = _out167;
            _1574_bodyIdents = _out168;
            _1575_bodyEnv = _out169;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1574_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1572_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1572_boundRName, _1568_over, _1573_bodyExpr);
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1576_toLabel = _source74.dtor_toLabel;
          unmatched74 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source75 = _1576_toLabel;
            bool unmatched75 = true;
            if (unmatched75) {
              if (_source75.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1577_lbl = _source75.dtor_value;
                unmatched75 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1577_lbl)));
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
          Dafny.ISequence<DAST._IStatement> _1578_body = _source74.dtor_body;
          unmatched74 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _1579_selfClone;
              DCOMP._IOwnership _1580___v88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1581___v89;
              RAST._IExpr _out170;
              DCOMP._IOwnership _out171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out172;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out170, out _out171, out _out172);
              _1579_selfClone = _out170;
              _1580___v88 = _out171;
              _1581___v89 = _out172;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1579_selfClone)));
            }
            newEnv = env;
            BigInteger _hi34 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1582_paramI = BigInteger.Zero; _1582_paramI < _hi34; _1582_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1583_param;
              _1583_param = ((env).dtor_names).Select(_1582_paramI);
              RAST._IExpr _1584_paramInit;
              DCOMP._IOwnership _1585___v90;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1586___v91;
              RAST._IExpr _out173;
              DCOMP._IOwnership _out174;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out175;
              (this).GenIdent(_1583_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out173, out _out174, out _out175);
              _1584_paramInit = _out173;
              _1585___v90 = _out174;
              _1586___v91 = _out175;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1583_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1584_paramInit)));
              if (((env).dtor_types).Contains(_1583_param)) {
                RAST._IType _1587_declaredType;
                _1587_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1583_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1583_param, _1587_declaredType);
              }
            }
            RAST._IExpr _1588_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1589_bodyIdents;
            DCOMP._IEnvironment _1590_bodyEnv;
            RAST._IExpr _out176;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
            DCOMP._IEnvironment _out178;
            (this).GenStmts(_1578_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out176, out _out177, out _out178);
            _1588_bodyExpr = _out176;
            _1589_bodyIdents = _out177;
            _1590_bodyEnv = _out178;
            readIdents = _1589_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1588_bodyExpr)));
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
          DAST._IExpression _1591_on = _source74.dtor_on;
          DAST._ICallName _1592_name = _source74.dtor_callName;
          Dafny.ISequence<DAST._IType> _1593_typeArgs = _source74.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1594_args = _source74.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1595_maybeOutVars = _source74.dtor_outs;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1596_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1597_recIdents;
            Dafny.ISequence<RAST._IType> _1598_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _1599_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out180;
            Dafny.ISequence<RAST._IType> _out181;
            Std.Wrappers._IOption<DAST._IResolvedType> _out182;
            (this).GenArgs(selfIdent, _1592_name, _1593_typeArgs, _1594_args, env, out _out179, out _out180, out _out181, out _out182);
            _1596_argExprs = _out179;
            _1597_recIdents = _out180;
            _1598_typeExprs = _out181;
            _1599_fullNameQualifier = _out182;
            readIdents = _1597_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source76 = _1599_fullNameQualifier;
            bool unmatched76 = true;
            if (unmatched76) {
              if (_source76.is_Some) {
                DAST._IResolvedType value9 = _source76.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1600_path = value9.dtor_path;
                Dafny.ISequence<DAST._IType> _1601_onTypeArgs = value9.dtor_typeArgs;
                DAST._IResolvedTypeBase _1602_base = value9.dtor_kind;
                unmatched76 = false;
                RAST._IExpr _1603_fullPath;
                RAST._IExpr _out183;
                _out183 = DCOMP.COMP.GenPathExpr(_1600_path);
                _1603_fullPath = _out183;
                Dafny.ISequence<RAST._IType> _1604_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out184;
                _out184 = (this).GenTypeArgs(_1601_onTypeArgs, DCOMP.GenTypeContext.@default());
                _1604_onTypeExprs = _out184;
                RAST._IExpr _1605_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _1606_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1607_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1602_base).is_Trait) || ((_1602_base).is_Class)) {
                  RAST._IExpr _out185;
                  DCOMP._IOwnership _out186;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out187;
                  (this).GenExpr(_1591_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out185, out _out186, out _out187);
                  _1605_onExpr = _out185;
                  _1606_recOwnership = _out186;
                  _1607_recIdents = _out187;
                  _1605_onExpr = ((this).modify__macro).Apply1(_1605_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1607_recIdents);
                } else {
                  RAST._IExpr _out188;
                  DCOMP._IOwnership _out189;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out190;
                  (this).GenExpr(_1591_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out188, out _out189, out _out190);
                  _1605_onExpr = _out188;
                  _1606_recOwnership = _out189;
                  _1607_recIdents = _out190;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1607_recIdents);
                }
                generated = ((((_1603_fullPath).ApplyType(_1604_onTypeExprs)).MSel(DCOMP.__default.escapeName((_1592_name).dtor_name))).ApplyType(_1598_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_1605_onExpr), _1596_argExprs));
              }
            }
            if (unmatched76) {
              unmatched76 = false;
              RAST._IExpr _1608_onExpr;
              DCOMP._IOwnership _1609___v96;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1610_enclosingIdents;
              RAST._IExpr _out191;
              DCOMP._IOwnership _out192;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out193;
              (this).GenExpr(_1591_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out191, out _out192, out _out193);
              _1608_onExpr = _out191;
              _1609___v96 = _out192;
              _1610_enclosingIdents = _out193;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1610_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _1611_renderedName;
              _1611_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
                DAST._ICallName _source77 = _1592_name;
                bool unmatched77 = true;
                if (unmatched77) {
                  if (_source77.is_CallName) {
                    Dafny.ISequence<Dafny.Rune> _1612_name = _source77.dtor_name;
                    unmatched77 = false;
                    return DCOMP.__default.escapeName(_1612_name);
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
              DAST._IExpression _source78 = _1591_on;
              bool unmatched78 = true;
              if (unmatched78) {
                if (_source78.is_Companion) {
                  unmatched78 = false;
                  {
                    _1608_onExpr = (_1608_onExpr).MSel(_1611_renderedName);
                  }
                }
              }
              if (unmatched78) {
                unmatched78 = false;
                {
                  if (!object.Equals(_1608_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source79 = _1592_name;
                    bool unmatched79 = true;
                    if (unmatched79) {
                      if (_source79.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source79.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _1613_tpe = onType0.dtor_value;
                          unmatched79 = false;
                          RAST._IType _1614_typ;
                          RAST._IType _out194;
                          _out194 = (this).GenType(_1613_tpe, DCOMP.GenTypeContext.@default());
                          _1614_typ = _out194;
                          if (((_1614_typ).IsObjectOrPointer()) && (!object.Equals(_1608_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _1608_onExpr = ((this).modify__macro).Apply1(_1608_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched79) {
                      unmatched79 = false;
                    }
                  }
                  _1608_onExpr = (_1608_onExpr).Sel(_1611_renderedName);
                }
              }
              generated = ((_1608_onExpr).ApplyType(_1598_typeExprs)).Apply(_1596_argExprs);
            }
            if (((_1595_maybeOutVars).is_Some) && ((new BigInteger(((_1595_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1615_outVar;
              _1615_outVar = DCOMP.__default.escapeName((((_1595_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
              if (!((env).CanReadWithoutClone(_1615_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1615_outVar, generated);
            } else if (((_1595_maybeOutVars).is_None) || ((new BigInteger(((_1595_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1616_tmpVar;
              _1616_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1617_tmpId;
              _1617_tmpId = RAST.Expr.create_Identifier(_1616_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1616_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1618_outVars;
              _1618_outVars = (_1595_maybeOutVars).dtor_value;
              BigInteger _hi35 = new BigInteger((_1618_outVars).Count);
              for (BigInteger _1619_outI = BigInteger.Zero; _1619_outI < _hi35; _1619_outI++) {
                Dafny.ISequence<Dafny.Rune> _1620_outVar;
                _1620_outVar = DCOMP.__default.escapeName(((_1618_outVars).Select(_1619_outI)));
                RAST._IExpr _1621_rhs;
                _1621_rhs = (_1617_tmpId).Sel(Std.Strings.__default.OfNat(_1619_outI));
                if (!((env).CanReadWithoutClone(_1620_outVar))) {
                  _1621_rhs = RAST.__default.MaybePlacebo(_1621_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1620_outVar, _1621_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Return) {
          DAST._IExpression _1622_exprDafny = _source74.dtor_expr;
          unmatched74 = false;
          {
            RAST._IExpr _1623_expr;
            DCOMP._IOwnership _1624___v107;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1625_recIdents;
            RAST._IExpr _out195;
            DCOMP._IOwnership _out196;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out197;
            (this).GenExpr(_1622_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out195, out _out196, out _out197);
            _1623_expr = _out195;
            _1624___v107 = _out196;
            _1625_recIdents = _out197;
            readIdents = _1625_recIdents;
            if (isLast) {
              generated = _1623_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1623_expr));
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
        DAST._IExpression _1626_e = _source74.dtor_Print_a0;
        unmatched74 = false;
        {
          RAST._IExpr _1627_printedExpr;
          DCOMP._IOwnership _1628_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1629_recIdents;
          RAST._IExpr _out198;
          DCOMP._IOwnership _out199;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out200;
          (this).GenExpr(_1626_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out198, out _out199, out _out200);
          _1627_printedExpr = _out198;
          _1628_recOwnership = _out199;
          _1629_recIdents = _out200;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1627_printedExpr)));
          readIdents = _1629_recIdents;
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
            bool _1630_b = _h170.dtor_BoolLiteral_a0;
            unmatched81 = false;
            {
              RAST._IExpr _out205;
              DCOMP._IOwnership _out206;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_1630_b), expectedOwnership, out _out205, out _out206);
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
            Dafny.ISequence<Dafny.Rune> _1631_i = _h171.dtor_IntLiteral_a0;
            DAST._IType _1632_t = _h171.dtor_IntLiteral_a1;
            unmatched81 = false;
            {
              DAST._IType _source82 = _1632_t;
              bool unmatched82 = true;
              if (unmatched82) {
                if (_source82.is_Primitive) {
                  DAST._IPrimitive _h70 = _source82.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    unmatched82 = false;
                    {
                      if ((new BigInteger((_1631_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1631_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1631_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched82) {
                DAST._IType _1633_o = _source82;
                unmatched82 = false;
                {
                  RAST._IType _1634_genType;
                  RAST._IType _out207;
                  _out207 = (this).GenType(_1633_o, DCOMP.GenTypeContext.@default());
                  _1634_genType = _out207;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1631_i), _1634_genType);
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
            Dafny.ISequence<Dafny.Rune> _1635_n = _h172.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1636_d = _h172.dtor_DecLiteral_a1;
            DAST._IType _1637_t = _h172.dtor_DecLiteral_a2;
            unmatched81 = false;
            {
              DAST._IType _source83 = _1637_t;
              bool unmatched83 = true;
              if (unmatched83) {
                if (_source83.is_Primitive) {
                  DAST._IPrimitive _h71 = _source83.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    unmatched83 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1635_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1636_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched83) {
                DAST._IType _1638_o = _source83;
                unmatched83 = false;
                {
                  RAST._IType _1639_genType;
                  RAST._IType _out210;
                  _out210 = (this).GenType(_1638_o, DCOMP.GenTypeContext.@default());
                  _1639_genType = _out210;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1635_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1636_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1639_genType);
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
            Dafny.ISequence<Dafny.Rune> _1640_l = _h173.dtor_StringLiteral_a0;
            bool _1641_verbatim = _h173.dtor_verbatim;
            unmatched81 = false;
            {
              if (_1641_verbatim) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Verbatim strings prefixed by @ not supported yet."));
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1640_l, false, _1641_verbatim));
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
            BigInteger _1642_c = _h174.dtor_CharLiteralUTF16_a0;
            unmatched81 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1642_c));
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
            Dafny.Rune _1643_c = _h175.dtor_CharLiteral_a0;
            unmatched81 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1643_c).Value)));
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
        DAST._IType _1644_tpe = _h176.dtor_Null_a0;
        unmatched81 = false;
        {
          RAST._IType _1645_tpeGen;
          RAST._IType _out219;
          _out219 = (this).GenType(_1644_tpe, DCOMP.GenTypeContext.@default());
          _1645_tpeGen = _out219;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null"));
          } else {
            r = RAST.Expr.create_TypeAscription(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _1645_tpeGen);
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
      DAST._IBinOp _1646_op = _let_tmp_rhs53.dtor_op;
      DAST._IExpression _1647_lExpr = _let_tmp_rhs53.dtor_left;
      DAST._IExpression _1648_rExpr = _let_tmp_rhs53.dtor_right;
      DAST.Format._IBinaryOpFormat _1649_format = _let_tmp_rhs53.dtor_format2;
      bool _1650_becomesLeftCallsRight;
      _1650_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source84 = _1646_op;
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
          unmatched84 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1651_becomesRightCallsLeft;
      _1651_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source85 = _1646_op;
        bool unmatched85 = true;
        if (unmatched85) {
          if (_source85.is_In) {
            unmatched85 = false;
            return true;
          }
        }
        if (unmatched85) {
          unmatched85 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1652_becomesCallLeftRight;
      _1652_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source86 = _1646_op;
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
          unmatched86 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      DCOMP._IOwnership _1653_expectedLeftOwnership;
      _1653_expectedLeftOwnership = ((_1650_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1651_becomesRightCallsLeft) || (_1652_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1654_expectedRightOwnership;
      _1654_expectedRightOwnership = (((_1650_becomesLeftCallsRight) || (_1652_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1651_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1655_left;
      DCOMP._IOwnership _1656___v112;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1657_recIdentsL;
      RAST._IExpr _out222;
      DCOMP._IOwnership _out223;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out224;
      (this).GenExpr(_1647_lExpr, selfIdent, env, _1653_expectedLeftOwnership, out _out222, out _out223, out _out224);
      _1655_left = _out222;
      _1656___v112 = _out223;
      _1657_recIdentsL = _out224;
      RAST._IExpr _1658_right;
      DCOMP._IOwnership _1659___v113;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1660_recIdentsR;
      RAST._IExpr _out225;
      DCOMP._IOwnership _out226;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out227;
      (this).GenExpr(_1648_rExpr, selfIdent, env, _1654_expectedRightOwnership, out _out225, out _out226, out _out227);
      _1658_right = _out225;
      _1659___v113 = _out226;
      _1660_recIdentsR = _out227;
      DAST._IBinOp _source87 = _1646_op;
      bool unmatched87 = true;
      if (unmatched87) {
        if (_source87.is_In) {
          unmatched87 = false;
          {
            r = ((_1658_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1655_left);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_SeqProperPrefix) {
          unmatched87 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1655_left, _1658_right, _1649_format);
        }
      }
      if (unmatched87) {
        if (_source87.is_SeqPrefix) {
          unmatched87 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1655_left, _1658_right, _1649_format);
        }
      }
      if (unmatched87) {
        if (_source87.is_SetMerge) {
          unmatched87 = false;
          {
            r = ((_1655_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1658_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_SetSubtraction) {
          unmatched87 = false;
          {
            r = ((_1655_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1658_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_SetIntersection) {
          unmatched87 = false;
          {
            r = ((_1655_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1658_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Subset) {
          unmatched87 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1655_left, _1658_right, _1649_format);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_ProperSubset) {
          unmatched87 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1655_left, _1658_right, _1649_format);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_SetDisjoint) {
          unmatched87 = false;
          {
            r = ((_1655_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1658_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MapMerge) {
          unmatched87 = false;
          {
            r = ((_1655_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1658_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MapSubtraction) {
          unmatched87 = false;
          {
            r = ((_1655_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1658_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MultisetMerge) {
          unmatched87 = false;
          {
            r = ((_1655_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1658_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MultisetSubtraction) {
          unmatched87 = false;
          {
            r = ((_1655_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1658_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MultisetIntersection) {
          unmatched87 = false;
          {
            r = ((_1655_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1658_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Submultiset) {
          unmatched87 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1655_left, _1658_right, _1649_format);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_ProperSubmultiset) {
          unmatched87 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1655_left, _1658_right, _1649_format);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MultisetDisjoint) {
          unmatched87 = false;
          {
            r = ((_1655_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1658_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Concat) {
          unmatched87 = false;
          {
            r = ((_1655_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1658_right);
          }
        }
      }
      if (unmatched87) {
        unmatched87 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1646_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1646_op), _1655_left, _1658_right, _1649_format);
          } else {
            DAST._IBinOp _source88 = _1646_op;
            bool unmatched88 = true;
            if (unmatched88) {
              if (_source88.is_Eq) {
                bool _1661_referential = _source88.dtor_referential;
                unmatched88 = false;
                {
                  if (_1661_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1655_left, _1658_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_1648_rExpr).is_SeqValue) && ((new BigInteger(((_1648_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1655_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1647_lExpr).is_SeqValue) && ((new BigInteger(((_1647_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1658_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1655_left, _1658_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
              }
            }
            if (unmatched88) {
              if (_source88.is_EuclidianDiv) {
                unmatched88 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1655_left, _1658_right));
                }
              }
            }
            if (unmatched88) {
              if (_source88.is_EuclidianMod) {
                unmatched88 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1655_left, _1658_right));
                }
              }
            }
            if (unmatched88) {
              Dafny.ISequence<Dafny.Rune> _1662_op = _source88.dtor_Passthrough_a0;
              unmatched88 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1662_op, _1655_left, _1658_right, _1649_format);
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
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1657_recIdentsL, _1660_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IExpression _1663_expr = _let_tmp_rhs54.dtor_value;
      DAST._IType _1664_fromTpe = _let_tmp_rhs54.dtor_from;
      DAST._IType _1665_toTpe = _let_tmp_rhs54.dtor_typ;
      DAST._IType _let_tmp_rhs55 = _1665_toTpe;
      DAST._IResolvedType _let_tmp_rhs56 = _let_tmp_rhs55.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1666_path = _let_tmp_rhs56.dtor_path;
      Dafny.ISequence<DAST._IType> _1667_typeArgs = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs57 = _let_tmp_rhs56.dtor_kind;
      DAST._IType _1668_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _1669_range = _let_tmp_rhs57.dtor_range;
      bool _1670_erase = _let_tmp_rhs57.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1671___v115 = _let_tmp_rhs56.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1672___v116 = _let_tmp_rhs56.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1673___v117 = _let_tmp_rhs56.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1674_nativeToType;
      _1674_nativeToType = DCOMP.COMP.NewtypeToRustType(_1668_b, _1669_range);
      if (object.Equals(_1664_fromTpe, _1668_b)) {
        RAST._IExpr _1675_recursiveGen;
        DCOMP._IOwnership _1676_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1677_recIdents;
        RAST._IExpr _out230;
        DCOMP._IOwnership _out231;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out232;
        (this).GenExpr(_1663_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out230, out _out231, out _out232);
        _1675_recursiveGen = _out230;
        _1676_recOwned = _out231;
        _1677_recIdents = _out232;
        readIdents = _1677_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source89 = _1674_nativeToType;
        bool unmatched89 = true;
        if (unmatched89) {
          if (_source89.is_Some) {
            RAST._IType _1678_v = _source89.dtor_value;
            unmatched89 = false;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1675_recursiveGen, RAST.Expr.create_ExprFromType(_1678_v)));
            RAST._IExpr _out233;
            DCOMP._IOwnership _out234;
            (this).FromOwned(r, expectedOwnership, out _out233, out _out234);
            r = _out233;
            resultingOwnership = _out234;
          }
        }
        if (unmatched89) {
          unmatched89 = false;
          if (_1670_erase) {
            r = _1675_recursiveGen;
          } else {
            RAST._IType _1679_rhsType;
            RAST._IType _out235;
            _out235 = (this).GenType(_1665_toTpe, DCOMP.GenTypeContext.InBinding());
            _1679_rhsType = _out235;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1679_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1675_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out236;
          DCOMP._IOwnership _out237;
          (this).FromOwnership(r, _1676_recOwned, expectedOwnership, out _out236, out _out237);
          r = _out236;
          resultingOwnership = _out237;
        }
      } else {
        if ((_1674_nativeToType).is_Some) {
          DAST._IType _source90 = _1664_fromTpe;
          bool unmatched90 = true;
          if (unmatched90) {
            if (_source90.is_UserDefined) {
              DAST._IResolvedType resolved1 = _source90.dtor_resolved;
              DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
              if (kind1.is_Newtype) {
                DAST._IType _1680_b0 = kind1.dtor_baseType;
                DAST._INewtypeRange _1681_range0 = kind1.dtor_range;
                bool _1682_erase0 = kind1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1683_attributes0 = resolved1.dtor_attributes;
                unmatched90 = false;
                {
                  Std.Wrappers._IOption<RAST._IType> _1684_nativeFromType;
                  _1684_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1680_b0, _1681_range0);
                  if ((_1684_nativeFromType).is_Some) {
                    RAST._IExpr _1685_recursiveGen;
                    DCOMP._IOwnership _1686_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1687_recIdents;
                    RAST._IExpr _out238;
                    DCOMP._IOwnership _out239;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out240;
                    (this).GenExpr(_1663_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out238, out _out239, out _out240);
                    _1685_recursiveGen = _out238;
                    _1686_recOwned = _out239;
                    _1687_recIdents = _out240;
                    RAST._IExpr _out241;
                    DCOMP._IOwnership _out242;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_1685_recursiveGen, (_1674_nativeToType).dtor_value), _1686_recOwned, expectedOwnership, out _out241, out _out242);
                    r = _out241;
                    resultingOwnership = _out242;
                    readIdents = _1687_recIdents;
                    return ;
                  }
                }
              }
            }
          }
          if (unmatched90) {
            unmatched90 = false;
          }
          if (object.Equals(_1664_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1688_recursiveGen;
            DCOMP._IOwnership _1689_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1690_recIdents;
            RAST._IExpr _out243;
            DCOMP._IOwnership _out244;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out245;
            (this).GenExpr(_1663_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out243, out _out244, out _out245);
            _1688_recursiveGen = _out243;
            _1689_recOwned = _out244;
            _1690_recIdents = _out245;
            RAST._IExpr _out246;
            DCOMP._IOwnership _out247;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_1688_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1674_nativeToType).dtor_value), _1689_recOwned, expectedOwnership, out _out246, out _out247);
            r = _out246;
            resultingOwnership = _out247;
            readIdents = _1690_recIdents;
            return ;
          }
        }
        RAST._IExpr _out248;
        DCOMP._IOwnership _out249;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out250;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1663_expr, _1664_fromTpe, _1668_b), _1668_b, _1665_toTpe), selfIdent, env, expectedOwnership, out _out248, out _out249, out _out250);
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
      DAST._IExpression _1691_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _1692_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _1693_toTpe = _let_tmp_rhs58.dtor_typ;
      DAST._IType _let_tmp_rhs59 = _1692_fromTpe;
      DAST._IResolvedType _let_tmp_rhs60 = _let_tmp_rhs59.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1694___v123 = _let_tmp_rhs60.dtor_path;
      Dafny.ISequence<DAST._IType> _1695___v124 = _let_tmp_rhs60.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs61 = _let_tmp_rhs60.dtor_kind;
      DAST._IType _1696_b = _let_tmp_rhs61.dtor_baseType;
      DAST._INewtypeRange _1697_range = _let_tmp_rhs61.dtor_range;
      bool _1698_erase = _let_tmp_rhs61.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1699_attributes = _let_tmp_rhs60.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1700___v125 = _let_tmp_rhs60.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1701___v126 = _let_tmp_rhs60.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1702_nativeFromType;
      _1702_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1696_b, _1697_range);
      if (object.Equals(_1696_b, _1693_toTpe)) {
        RAST._IExpr _1703_recursiveGen;
        DCOMP._IOwnership _1704_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1705_recIdents;
        RAST._IExpr _out251;
        DCOMP._IOwnership _out252;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out253;
        (this).GenExpr(_1691_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out251, out _out252, out _out253);
        _1703_recursiveGen = _out251;
        _1704_recOwned = _out252;
        _1705_recIdents = _out253;
        readIdents = _1705_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source91 = _1702_nativeFromType;
        bool unmatched91 = true;
        if (unmatched91) {
          if (_source91.is_Some) {
            RAST._IType _1706_v = _source91.dtor_value;
            unmatched91 = false;
            RAST._IType _1707_toTpeRust;
            RAST._IType _out254;
            _out254 = (this).GenType(_1693_toTpe, DCOMP.GenTypeContext.@default());
            _1707_toTpeRust = _out254;
            r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1707_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1703_recursiveGen));
            RAST._IExpr _out255;
            DCOMP._IOwnership _out256;
            (this).FromOwned(r, expectedOwnership, out _out255, out _out256);
            r = _out255;
            resultingOwnership = _out256;
          }
        }
        if (unmatched91) {
          unmatched91 = false;
          if (_1698_erase) {
            r = _1703_recursiveGen;
          } else {
            r = (_1703_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out257;
          DCOMP._IOwnership _out258;
          (this).FromOwnership(r, _1704_recOwned, expectedOwnership, out _out257, out _out258);
          r = _out257;
          resultingOwnership = _out258;
        }
      } else {
        if ((_1702_nativeFromType).is_Some) {
          if (object.Equals(_1693_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1708_recursiveGen;
            DCOMP._IOwnership _1709_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1710_recIdents;
            RAST._IExpr _out259;
            DCOMP._IOwnership _out260;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out261;
            (this).GenExpr(_1691_expr, selfIdent, env, expectedOwnership, out _out259, out _out260, out _out261);
            _1708_recursiveGen = _out259;
            _1709_recOwned = _out260;
            _1710_recIdents = _out261;
            RAST._IExpr _out262;
            DCOMP._IOwnership _out263;
            (this).FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1708_recursiveGen, (this).DafnyCharUnderlying)), _1709_recOwned, expectedOwnership, out _out262, out _out263);
            r = _out262;
            resultingOwnership = _out263;
            readIdents = _1710_recIdents;
            return ;
          }
        }
        RAST._IExpr _out264;
        DCOMP._IOwnership _out265;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out266;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1691_expr, _1692_fromTpe, _1696_b), _1696_b, _1693_toTpe), selfIdent, env, expectedOwnership, out _out264, out _out265, out _out266);
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
        Std.Wrappers._IResult<__T, __E> _1711_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_1711_valueOrError0).IsFailure()) {
          return (_1711_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1712_head = (_1711_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _1713_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_1713_valueOrError1).IsFailure()) {
            return (_1713_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _1714_tail = (_1713_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1712_head), _1714_tail));
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
          RAST._IType _1715_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          RAST._IType _1716_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel((this).upcast)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1715_fromTpeUnderlying, _1716_toTpeUnderlying))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1717_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_1717_valueOrError0).IsFailure()) {
          return (_1717_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1718_lambda = (_1717_valueOrError0).Extract();
          if ((fromType).is_Arrow) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(_1718_lambda);
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).Apply1(_1718_lambda));
          }
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1719_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim12 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr12 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
          for (int i12 = 0; i12 < dim12; i12++) {
            var _1720_i = (BigInteger) i12;
            arr12[(int)(_1720_i)] = (this).UpcastConversionLambda((((fromType).dtor_resolved).dtor_typeArgs).Select(_1720_i), ((fromTpe).dtor_arguments).Select(_1720_i), (((toType).dtor_resolved).dtor_typeArgs).Select(_1720_i), ((toTpe).dtor_arguments).Select(_1720_i), typeParams);
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr12);
        }))());
        if ((_1719_valueOrError1).IsFailure()) {
          return (_1719_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _1721_lambdas = (_1719_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim13 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr13 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim13, "array size exceeds memory limit")];
  for (int i13 = 0; i13 < dim13; i13++) {
    var _1722_i = (BigInteger) i13;
    arr13[(int)(_1722_i)] = ((fromTpe).dtor_arguments).Select(_1722_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr13);
}))())).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_1721_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _1723_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _1724_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _1725_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _1726_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1727_valueOrError2 = (this).UpcastConversionLambda(_1725_newFromType, _1723_newFromTpe, _1726_newToType, _1724_newToTpe, typeParams);
        if ((_1727_valueOrError2).IsFailure()) {
          return (_1727_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1728_coerceArg = (_1727_valueOrError2).Extract();
          RAST._IExpr _1729_collectionType = (RAST.__default.dafny__runtime).MSel(((fromTpe).dtor_baseName).dtor_name);
          RAST._IExpr _1730_baseType = (((((fromTpe).dtor_baseName).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? ((_1729_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((fromTpe).dtor_arguments).Select(BigInteger.Zero), _1723_newFromTpe))) : ((_1729_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1723_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_1730_baseType).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_1728_coerceArg));
        }
      } else if ((((((((((fromTpe).is_DynType) && (((fromTpe).dtor_underlying).is_FnType)) && ((toTpe).is_DynType)) && (((toTpe).dtor_underlying).is_FnType)) && ((((fromTpe).dtor_underlying).dtor_arguments).Equals(((toTpe).dtor_underlying).dtor_arguments))) && ((fromType).is_Arrow)) && ((toType).is_Arrow)) && ((new BigInteger((((fromTpe).dtor_underlying).dtor_arguments).Count)) == (BigInteger.One))) && (((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).is_Borrowed)) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1731_valueOrError3 = (this).UpcastConversionLambda((fromType).dtor_result, ((fromTpe).dtor_underlying).dtor_returnType, (toType).dtor_result, ((toTpe).dtor_underlying).dtor_returnType, typeParams);
        if ((_1731_valueOrError3).IsFailure()) {
          return (_1731_valueOrError3).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1732_lambda = (_1731_valueOrError3).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn1_coerce"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying, ((fromTpe).dtor_underlying).dtor_returnType, ((toTpe).dtor_underlying).dtor_returnType))).Apply1(_1732_lambda));
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
      DAST._IExpression _1733_expr = _let_tmp_rhs62.dtor_value;
      DAST._IType _1734_fromTpe = _let_tmp_rhs62.dtor_from;
      DAST._IType _1735_toTpe = _let_tmp_rhs62.dtor_typ;
      RAST._IType _1736_fromTpeGen;
      RAST._IType _out267;
      _out267 = (this).GenType(_1734_fromTpe, DCOMP.GenTypeContext.InBinding());
      _1736_fromTpeGen = _out267;
      RAST._IType _1737_toTpeGen;
      RAST._IType _out268;
      _out268 = (this).GenType(_1735_toTpe, DCOMP.GenTypeContext.InBinding());
      _1737_toTpeGen = _out268;
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1738_upcastConverter;
      _1738_upcastConverter = (this).UpcastConversionLambda(_1734_fromTpe, _1736_fromTpeGen, _1735_toTpe, _1737_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_1738_upcastConverter).is_Success) {
        RAST._IExpr _1739_conversionLambda;
        _1739_conversionLambda = (_1738_upcastConverter).dtor_value;
        RAST._IExpr _1740_recursiveGen;
        DCOMP._IOwnership _1741_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1742_recIdents;
        RAST._IExpr _out269;
        DCOMP._IOwnership _out270;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out271;
        (this).GenExpr(_1733_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out269, out _out270, out _out271);
        _1740_recursiveGen = _out269;
        _1741_recOwned = _out270;
        _1742_recIdents = _out271;
        readIdents = _1742_recIdents;
        r = (_1739_conversionLambda).Apply1(_1740_recursiveGen);
        RAST._IExpr _out272;
        DCOMP._IOwnership _out273;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out272, out _out273);
        r = _out272;
        resultingOwnership = _out273;
      } else if ((this).IsDowncastConversion(_1736_fromTpeGen, _1737_toTpeGen)) {
        RAST._IExpr _1743_recursiveGen;
        DCOMP._IOwnership _1744_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1745_recIdents;
        RAST._IExpr _out274;
        DCOMP._IOwnership _out275;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out276;
        (this).GenExpr(_1733_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out274, out _out275, out _out276);
        _1743_recursiveGen = _out274;
        _1744_recOwned = _out275;
        _1745_recIdents = _out276;
        readIdents = _1745_recIdents;
        _1737_toTpeGen = (_1737_toTpeGen).ObjectOrPointerUnderlying();
        r = ((RAST.__default.dafny__runtime).MSel((this).downcast)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1743_recursiveGen, RAST.Expr.create_ExprFromType(_1737_toTpeGen)));
        RAST._IExpr _out277;
        DCOMP._IOwnership _out278;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out277, out _out278);
        r = _out277;
        resultingOwnership = _out278;
      } else {
        RAST._IExpr _1746_recursiveGen;
        DCOMP._IOwnership _1747_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1748_recIdents;
        RAST._IExpr _out279;
        DCOMP._IOwnership _out280;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out281;
        (this).GenExpr(_1733_expr, selfIdent, env, expectedOwnership, out _out279, out _out280, out _out281);
        _1746_recursiveGen = _out279;
        _1747_recOwned = _out280;
        _1748_recIdents = _out281;
        readIdents = _1748_recIdents;
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _let_tmp_rhs63 = _1738_upcastConverter;
        _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>> _let_tmp_rhs64 = _let_tmp_rhs63.dtor_error;
        DAST._IType _1749_fromType = _let_tmp_rhs64.dtor__0;
        RAST._IType _1750_fromTpeGen = _let_tmp_rhs64.dtor__1;
        DAST._IType _1751_toType = _let_tmp_rhs64.dtor__2;
        RAST._IType _1752_toTpeGen = _let_tmp_rhs64.dtor__3;
        Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1753_m = _let_tmp_rhs64.dtor__4;
        Dafny.ISequence<Dafny.Rune> _1754_msg;
        _1754_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1750_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1752_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1754_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1746_recursiveGen)._ToString(DCOMP.__default.IND), _1754_msg));
        RAST._IExpr _out282;
        DCOMP._IOwnership _out283;
        (this).FromOwnership(r, _1747_recOwned, expectedOwnership, out _out282, out _out283);
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
      DAST._IExpression _1755_expr = _let_tmp_rhs65.dtor_value;
      DAST._IType _1756_fromTpe = _let_tmp_rhs65.dtor_from;
      DAST._IType _1757_toTpe = _let_tmp_rhs65.dtor_typ;
      if (object.Equals(_1756_fromTpe, _1757_toTpe)) {
        RAST._IExpr _1758_recursiveGen;
        DCOMP._IOwnership _1759_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1760_recIdents;
        RAST._IExpr _out284;
        DCOMP._IOwnership _out285;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out286;
        (this).GenExpr(_1755_expr, selfIdent, env, expectedOwnership, out _out284, out _out285, out _out286);
        _1758_recursiveGen = _out284;
        _1759_recOwned = _out285;
        _1760_recIdents = _out286;
        r = _1758_recursiveGen;
        RAST._IExpr _out287;
        DCOMP._IOwnership _out288;
        (this).FromOwnership(r, _1759_recOwned, expectedOwnership, out _out287, out _out288);
        r = _out287;
        resultingOwnership = _out288;
        readIdents = _1760_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source92 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1756_fromTpe, _1757_toTpe);
        bool unmatched92 = true;
        if (unmatched92) {
          DAST._IType _10 = _source92.dtor__1;
          if (_10.is_UserDefined) {
            DAST._IResolvedType resolved2 = _10.dtor_resolved;
            DAST._IResolvedTypeBase kind2 = resolved2.dtor_kind;
            if (kind2.is_Newtype) {
              DAST._IType _1761_b = kind2.dtor_baseType;
              DAST._INewtypeRange _1762_range = kind2.dtor_range;
              bool _1763_erase = kind2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1764_attributes = resolved2.dtor_attributes;
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
            DAST._IResolvedTypeBase kind3 = resolved3.dtor_kind;
            if (kind3.is_Newtype) {
              DAST._IType _1765_b = kind3.dtor_baseType;
              DAST._INewtypeRange _1766_range = kind3.dtor_range;
              bool _1767_erase = kind3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1768_attributes = resolved3.dtor_attributes;
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
                    RAST._IExpr _1769_recursiveGen;
                    DCOMP._IOwnership _1770___v137;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1771_recIdents;
                    RAST._IExpr _out295;
                    DCOMP._IOwnership _out296;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out297;
                    (this).GenExpr(_1755_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out295, out _out296, out _out297);
                    _1769_recursiveGen = _out295;
                    _1770___v137 = _out296;
                    _1771_recIdents = _out297;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1769_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out298;
                    DCOMP._IOwnership _out299;
                    (this).FromOwned(r, expectedOwnership, out _out298, out _out299);
                    r = _out298;
                    resultingOwnership = _out299;
                    readIdents = _1771_recIdents;
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
                    RAST._IExpr _1772_recursiveGen;
                    DCOMP._IOwnership _1773___v138;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1774_recIdents;
                    RAST._IExpr _out300;
                    DCOMP._IOwnership _out301;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out302;
                    (this).GenExpr(_1755_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out300, out _out301, out _out302);
                    _1772_recursiveGen = _out300;
                    _1773___v138 = _out301;
                    _1774_recIdents = _out302;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1772_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out303;
                    DCOMP._IOwnership _out304;
                    (this).FromOwned(r, expectedOwnership, out _out303, out _out304);
                    r = _out303;
                    resultingOwnership = _out304;
                    readIdents = _1774_recIdents;
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
                unmatched92 = false;
                {
                  RAST._IType _1775_rhsType;
                  RAST._IType _out305;
                  _out305 = (this).GenType(_1757_toTpe, DCOMP.GenTypeContext.InBinding());
                  _1775_rhsType = _out305;
                  RAST._IExpr _1776_recursiveGen;
                  DCOMP._IOwnership _1777___v140;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1778_recIdents;
                  RAST._IExpr _out306;
                  DCOMP._IOwnership _out307;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out308;
                  (this).GenExpr(_1755_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out306, out _out307, out _out308);
                  _1776_recursiveGen = _out306;
                  _1777___v140 = _out307;
                  _1778_recIdents = _out308;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1775_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1776_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out309;
                  DCOMP._IOwnership _out310;
                  (this).FromOwned(r, expectedOwnership, out _out309, out _out310);
                  r = _out309;
                  resultingOwnership = _out310;
                  readIdents = _1778_recIdents;
                }
              }
            }
          }
        }
        if (unmatched92) {
          DAST._IType _04 = _source92.dtor__0;
          if (_04.is_Passthrough) {
            DAST._IType _14 = _source92.dtor__1;
            if (_14.is_Primitive) {
              DAST._IPrimitive _h77 = _14.dtor_Primitive_a0;
              if (_h77.is_Int) {
                unmatched92 = false;
                {
                  RAST._IType _1779_rhsType;
                  RAST._IType _out311;
                  _out311 = (this).GenType(_1756_fromTpe, DCOMP.GenTypeContext.InBinding());
                  _1779_rhsType = _out311;
                  RAST._IExpr _1780_recursiveGen;
                  DCOMP._IOwnership _1781___v142;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1782_recIdents;
                  RAST._IExpr _out312;
                  DCOMP._IOwnership _out313;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out314;
                  (this).GenExpr(_1755_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out312, out _out313, out _out314);
                  _1780_recursiveGen = _out312;
                  _1781___v142 = _out313;
                  _1782_recIdents = _out314;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_1780_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out315;
                  DCOMP._IOwnership _out316;
                  (this).FromOwned(r, expectedOwnership, out _out315, out _out316);
                  r = _out315;
                  resultingOwnership = _out316;
                  readIdents = _1782_recIdents;
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
                    RAST._IType _1783_rhsType;
                    RAST._IType _out317;
                    _out317 = (this).GenType(_1757_toTpe, DCOMP.GenTypeContext.InBinding());
                    _1783_rhsType = _out317;
                    RAST._IExpr _1784_recursiveGen;
                    DCOMP._IOwnership _1785___v143;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1786_recIdents;
                    RAST._IExpr _out318;
                    DCOMP._IOwnership _out319;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out320;
                    (this).GenExpr(_1755_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out318, out _out319, out _out320);
                    _1784_recursiveGen = _out318;
                    _1785___v143 = _out319;
                    _1786_recIdents = _out320;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1784_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out321;
                    DCOMP._IOwnership _out322;
                    (this).FromOwned(r, expectedOwnership, out _out321, out _out322);
                    r = _out321;
                    resultingOwnership = _out322;
                    readIdents = _1786_recIdents;
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
                    RAST._IType _1787_rhsType;
                    RAST._IType _out323;
                    _out323 = (this).GenType(_1756_fromTpe, DCOMP.GenTypeContext.InBinding());
                    _1787_rhsType = _out323;
                    RAST._IExpr _1788_recursiveGen;
                    DCOMP._IOwnership _1789___v144;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1790_recIdents;
                    RAST._IExpr _out324;
                    DCOMP._IOwnership _out325;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out326;
                    (this).GenExpr(_1755_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out324, out _out325, out _out326);
                    _1788_recursiveGen = _out324;
                    _1789___v144 = _out325;
                    _1790_recIdents = _out326;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1788_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out327;
                    DCOMP._IOwnership _out328;
                    (this).FromOwned(r, expectedOwnership, out _out327, out _out328);
                    r = _out327;
                    resultingOwnership = _out328;
                    readIdents = _1790_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched92) {
          DAST._IType _07 = _source92.dtor__0;
          if (_07.is_Passthrough) {
            DAST._IType _17 = _source92.dtor__1;
            if (_17.is_Passthrough) {
              unmatched92 = false;
              {
                RAST._IExpr _1791_recursiveGen;
                DCOMP._IOwnership _1792___v147;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1793_recIdents;
                RAST._IExpr _out329;
                DCOMP._IOwnership _out330;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
                (this).GenExpr(_1755_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out329, out _out330, out _out331);
                _1791_recursiveGen = _out329;
                _1792___v147 = _out330;
                _1793_recIdents = _out331;
                RAST._IType _1794_toTpeGen;
                RAST._IType _out332;
                _out332 = (this).GenType(_1757_toTpe, DCOMP.GenTypeContext.InBinding());
                _1794_toTpeGen = _out332;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1791_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1794_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out333;
                DCOMP._IOwnership _out334;
                (this).FromOwned(r, expectedOwnership, out _out333, out _out334);
                r = _out333;
                resultingOwnership = _out334;
                readIdents = _1793_recIdents;
              }
            }
          }
        }
        if (unmatched92) {
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
      Std.Wrappers._IOption<RAST._IType> _1795_tpe;
      _1795_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1796_placeboOpt;
      _1796_placeboOpt = (((_1795_tpe).is_Some) ? (((_1795_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _1797_currentlyBorrowed;
      _1797_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1798_noNeedOfClone;
      _1798_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1796_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _1797_currentlyBorrowed = false;
        _1798_noNeedOfClone = true;
        _1795_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_1796_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = ((_1797_currentlyBorrowed) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()));
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_1795_tpe).is_Some) && (((_1795_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _1799_needObjectFromRef;
        _1799_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source93 = (selfIdent).dtor_dafnyType;
          bool unmatched93 = true;
          if (unmatched93) {
            if (_source93.is_UserDefined) {
              DAST._IResolvedType resolved4 = _source93.dtor_resolved;
              DAST._IResolvedTypeBase _1800_base = resolved4.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _1801_attributes = resolved4.dtor_attributes;
              unmatched93 = false;
              return ((_1800_base).is_Class) || ((_1800_base).is_Trait);
            }
          }
          if (unmatched93) {
            unmatched93 = false;
            return false;
          }
          throw new System.Exception("unexpected control point");
        }))());
        if (_1799_needObjectFromRef) {
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_1798_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1798_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1797_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_1795_tpe).is_Some) && (((_1795_tpe).dtor_value).IsPointer())) {
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
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_1802_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_1802_attributes).UniqueElements, false, (((_exists_var_1) => {
        DAST._IAttribute _1803_attribute = (DAST._IAttribute)_exists_var_1;
        return ((_1802_attributes).Contains(_1803_attribute)) && ((((_1803_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_1803_attribute).dtor_args).Count)) == (new BigInteger(2))));
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
      for (BigInteger _1804_i = BigInteger.Zero; _1804_i < _hi36; _1804_i++) {
        DCOMP._IOwnership _1805_argOwnership;
        _1805_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if (((name).is_CallName) && ((_1804_i) < (new BigInteger((((name).dtor_signature)).Count)))) {
          RAST._IType _1806_tpe;
          RAST._IType _out338;
          _out338 = (this).GenType(((((name).dtor_signature)).Select(_1804_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _1806_tpe = _out338;
          if ((_1806_tpe).CanReadWithoutClone()) {
            _1805_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _1807_argExpr;
        DCOMP._IOwnership _1808___v154;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1809_argIdents;
        RAST._IExpr _out339;
        DCOMP._IOwnership _out340;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out341;
        (this).GenExpr((args).Select(_1804_i), selfIdent, env, _1805_argOwnership, out _out339, out _out340, out _out341);
        _1807_argExpr = _out339;
        _1808___v154 = _out340;
        _1809_argIdents = _out341;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1807_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1809_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi37 = new BigInteger((typeArgs).Count);
      for (BigInteger _1810_typeI = BigInteger.Zero; _1810_typeI < _hi37; _1810_typeI++) {
        RAST._IType _1811_typeExpr;
        RAST._IType _out342;
        _out342 = (this).GenType((typeArgs).Select(_1810_typeI), DCOMP.GenTypeContext.@default());
        _1811_typeExpr = _out342;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1811_typeExpr));
      }
      fullNameQualifier = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
        DAST._ICallName _source94 = name;
        bool unmatched94 = true;
        if (unmatched94) {
          if (_source94.is_CallName) {
            Dafny.ISequence<Dafny.Rune> _1812_nameIdent = _source94.dtor_name;
            Std.Wrappers._IOption<DAST._IType> onType1 = _source94.dtor_onType;
            if (onType1.is_Some) {
              DAST._IType value10 = onType1.dtor_value;
              if (value10.is_UserDefined) {
                DAST._IResolvedType _1813_resolvedType = value10.dtor_resolved;
                unmatched94 = false;
                if ((((_1813_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_1814_resolvedType, _1815_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(((_1814_resolvedType).dtor_properMethods).UniqueElements, true, (((_forall_var_8) => {
                  Dafny.ISequence<Dafny.Rune> _1816_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_8;
                  return !(((_1814_resolvedType).dtor_properMethods).Contains(_1816_m)) || (!object.Equals((_1816_m), _1815_nameIdent));
                }))))(_1813_resolvedType, _1812_nameIdent))) {
                  return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_1813_resolvedType, (_1812_nameIdent)), _1813_resolvedType));
                } else {
                  return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
                }
              }
            }
          }
        }
        if (unmatched94) {
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
          Dafny.ISequence<Dafny.Rune> _1817_name = _source95.dtor_Ident_a0;
          unmatched95 = false;
          {
            RAST._IExpr _out346;
            DCOMP._IOwnership _out347;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out348;
            (this).GenIdent(DCOMP.__default.escapeName(_1817_name), selfIdent, env, expectedOwnership, out _out346, out _out347, out _out348);
            r = _out346;
            resultingOwnership = _out347;
            readIdents = _out348;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1818_path = _source95.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _1819_typeArgs = _source95.dtor_typeArgs;
          unmatched95 = false;
          {
            RAST._IExpr _out349;
            _out349 = DCOMP.COMP.GenPathExpr(_1818_path);
            r = _out349;
            if ((new BigInteger((_1819_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1820_typeExprs;
              _1820_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi38 = new BigInteger((_1819_typeArgs).Count);
              for (BigInteger _1821_i = BigInteger.Zero; _1821_i < _hi38; _1821_i++) {
                RAST._IType _1822_typeExpr;
                RAST._IType _out350;
                _out350 = (this).GenType((_1819_typeArgs).Select(_1821_i), DCOMP.GenTypeContext.@default());
                _1822_typeExpr = _out350;
                _1820_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1820_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1822_typeExpr));
              }
              r = (r).ApplyType(_1820_typeExprs);
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
          DAST._IType _1823_typ = _source95.dtor_typ;
          unmatched95 = false;
          {
            RAST._IType _1824_typExpr;
            RAST._IType _out353;
            _out353 = (this).GenType(_1823_typ, DCOMP.GenTypeContext.@default());
            _1824_typExpr = _out353;
            if ((_1824_typExpr).IsObjectOrPointer()) {
              r = (_1824_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1824_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
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
          Dafny.ISequence<DAST._IExpression> _1825_values = _source95.dtor_Tuple_a0;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1826_exprs;
            _1826_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi39 = new BigInteger((_1825_values).Count);
            for (BigInteger _1827_i = BigInteger.Zero; _1827_i < _hi39; _1827_i++) {
              RAST._IExpr _1828_recursiveGen;
              DCOMP._IOwnership _1829___v159;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1830_recIdents;
              RAST._IExpr _out356;
              DCOMP._IOwnership _out357;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out358;
              (this).GenExpr((_1825_values).Select(_1827_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out356, out _out357, out _out358);
              _1828_recursiveGen = _out356;
              _1829___v159 = _out357;
              _1830_recIdents = _out358;
              _1826_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1826_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1828_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1830_recIdents);
            }
            r = (((new BigInteger((_1825_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_1826_exprs)) : (RAST.__default.SystemTuple(_1826_exprs)));
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
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1831_path = _source95.dtor_path;
          Dafny.ISequence<DAST._IType> _1832_typeArgs = _source95.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1833_args = _source95.dtor_args;
          unmatched95 = false;
          {
            RAST._IExpr _out361;
            _out361 = DCOMP.COMP.GenPathExpr(_1831_path);
            r = _out361;
            if ((new BigInteger((_1832_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1834_typeExprs;
              _1834_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi40 = new BigInteger((_1832_typeArgs).Count);
              for (BigInteger _1835_i = BigInteger.Zero; _1835_i < _hi40; _1835_i++) {
                RAST._IType _1836_typeExpr;
                RAST._IType _out362;
                _out362 = (this).GenType((_1832_typeArgs).Select(_1835_i), DCOMP.GenTypeContext.@default());
                _1836_typeExpr = _out362;
                _1834_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1834_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1836_typeExpr));
              }
              r = (r).ApplyType(_1834_typeExprs);
            }
            r = (r).MSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1837_arguments;
            _1837_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi41 = new BigInteger((_1833_args).Count);
            for (BigInteger _1838_i = BigInteger.Zero; _1838_i < _hi41; _1838_i++) {
              RAST._IExpr _1839_recursiveGen;
              DCOMP._IOwnership _1840___v160;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1841_recIdents;
              RAST._IExpr _out363;
              DCOMP._IOwnership _out364;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out365;
              (this).GenExpr((_1833_args).Select(_1838_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out363, out _out364, out _out365);
              _1839_recursiveGen = _out363;
              _1840___v160 = _out364;
              _1841_recIdents = _out365;
              _1837_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1837_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1839_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1841_recIdents);
            }
            r = (r).Apply(_1837_arguments);
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
          Dafny.ISequence<DAST._IExpression> _1842_dims = _source95.dtor_dims;
          DAST._IType _1843_typ = _source95.dtor_typ;
          unmatched95 = false;
          {
            if ((new BigInteger(16)) < (new BigInteger((_1842_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _1844_msg;
              _1844_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1844_msg);
              }
              r = RAST.Expr.create_RawExpr(_1844_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _1845_typeGen;
              RAST._IType _out368;
              _out368 = (this).GenType(_1843_typ, DCOMP.GenTypeContext.@default());
              _1845_typeGen = _out368;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _1846_dimExprs;
              _1846_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi42 = new BigInteger((_1842_dims).Count);
              for (BigInteger _1847_i = BigInteger.Zero; _1847_i < _hi42; _1847_i++) {
                RAST._IExpr _1848_recursiveGen;
                DCOMP._IOwnership _1849___v161;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1850_recIdents;
                RAST._IExpr _out369;
                DCOMP._IOwnership _out370;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out371;
                (this).GenExpr((_1842_dims).Select(_1847_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out369, out _out370, out _out371);
                _1848_recursiveGen = _out369;
                _1849___v161 = _out370;
                _1850_recIdents = _out371;
                _1846_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1846_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_TypeAscription(_1848_recursiveGen, RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("usize")))));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1850_recIdents);
              }
              if ((new BigInteger((_1842_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _1851_class__name;
                _1851_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_1842_dims).Count)));
                r = ((((RAST.__default.dafny__runtime).MSel(_1851_class__name)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1845_typeGen))).MSel((this).placebos__usize)).Apply(_1846_dimExprs);
              } else {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1845_typeGen))).Apply(_1846_dimExprs);
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
          DAST._IExpression _1852_underlying = _source95.dtor_value;
          unmatched95 = false;
          {
            RAST._IExpr _1853_recursiveGen;
            DCOMP._IOwnership _1854___v162;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1855_recIdents;
            RAST._IExpr _out374;
            DCOMP._IOwnership _out375;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out376;
            (this).GenExpr(_1852_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out374, out _out375, out _out376);
            _1853_recursiveGen = _out374;
            _1854___v162 = _out375;
            _1855_recIdents = _out376;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(_1853_recursiveGen);
            readIdents = _1855_recIdents;
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
          DAST._IExpression _1856_underlying = _source95.dtor_value;
          DAST._IType _1857_typ = _source95.dtor_typ;
          unmatched95 = false;
          {
            RAST._IType _1858_tpe;
            RAST._IType _out379;
            _out379 = (this).GenType(_1857_typ, DCOMP.GenTypeContext.@default());
            _1858_tpe = _out379;
            RAST._IExpr _1859_recursiveGen;
            DCOMP._IOwnership _1860___v163;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1861_recIdents;
            RAST._IExpr _out380;
            DCOMP._IOwnership _out381;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out382;
            (this).GenExpr(_1856_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out380, out _out381, out _out382);
            _1859_recursiveGen = _out380;
            _1860___v163 = _out381;
            _1861_recIdents = _out382;
            readIdents = _1861_recIdents;
            if ((_1858_tpe).IsObjectOrPointer()) {
              RAST._IType _1862_t;
              _1862_t = (_1858_tpe).ObjectOrPointerUnderlying();
              if ((_1862_t).is_Array) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).array__construct)).Apply1(_1859_recursiveGen);
              } else if ((_1862_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _1863_c;
                _1863_c = (_1862_t).MultiArrayClass();
                r = (((RAST.__default.dafny__runtime).MSel(_1863_c)).MSel((this).array__construct)).Apply1(_1859_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_1858_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_1858_tpe)._ToString(DCOMP.__default.IND)));
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
          DAST._IResolvedType _1864_datatypeType = _source95.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1865_typeArgs = _source95.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1866_variant = _source95.dtor_variant;
          bool _1867_isCo = _source95.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1868_values = _source95.dtor_contents;
          unmatched95 = false;
          {
            RAST._IExpr _out385;
            _out385 = DCOMP.COMP.GenPathExpr((_1864_datatypeType).dtor_path);
            r = _out385;
            Dafny.ISequence<RAST._IType> _1869_genTypeArgs;
            _1869_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi43 = new BigInteger((_1865_typeArgs).Count);
            for (BigInteger _1870_i = BigInteger.Zero; _1870_i < _hi43; _1870_i++) {
              RAST._IType _1871_typeExpr;
              RAST._IType _out386;
              _out386 = (this).GenType((_1865_typeArgs).Select(_1870_i), DCOMP.GenTypeContext.@default());
              _1871_typeExpr = _out386;
              _1869_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1869_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1871_typeExpr));
            }
            if ((new BigInteger((_1865_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1869_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1866_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1872_assignments;
            _1872_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi44 = new BigInteger((_1868_values).Count);
            for (BigInteger _1873_i = BigInteger.Zero; _1873_i < _hi44; _1873_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs66 = (_1868_values).Select(_1873_i);
              Dafny.ISequence<Dafny.Rune> _1874_name = _let_tmp_rhs66.dtor__0;
              DAST._IExpression _1875_value = _let_tmp_rhs66.dtor__1;
              if (_1867_isCo) {
                RAST._IExpr _1876_recursiveGen;
                DCOMP._IOwnership _1877___v164;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1878_recIdents;
                RAST._IExpr _out387;
                DCOMP._IOwnership _out388;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out389;
                (this).GenExpr(_1875_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out387, out _out388, out _out389);
                _1876_recursiveGen = _out387;
                _1877___v164 = _out388;
                _1878_recIdents = _out389;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1878_recIdents);
                Dafny.ISequence<Dafny.Rune> _1879_allReadCloned;
                _1879_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1878_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1880_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1878_recIdents).Elements) {
                    _1880_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1878_recIdents).Contains(_1880_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4331)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1879_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1879_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1880_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1880_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1878_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1878_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1880_next));
                }
                Dafny.ISequence<Dafny.Rune> _1881_wasAssigned;
                _1881_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1879_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1876_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1872_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1872_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1874_name), RAST.Expr.create_RawExpr(_1881_wasAssigned))));
              } else {
                RAST._IExpr _1882_recursiveGen;
                DCOMP._IOwnership _1883___v165;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1884_recIdents;
                RAST._IExpr _out390;
                DCOMP._IOwnership _out391;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out392;
                (this).GenExpr(_1875_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out390, out _out391, out _out392);
                _1882_recursiveGen = _out390;
                _1883___v165 = _out391;
                _1884_recIdents = _out392;
                _1872_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1872_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1874_name), _1882_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1884_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1872_assignments);
            if ((this).IsRcWrapped((_1864_datatypeType).dtor_attributes)) {
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
          DAST._IExpression _1885_length = _source95.dtor_length;
          DAST._IExpression _1886_expr = _source95.dtor_elem;
          unmatched95 = false;
          {
            RAST._IExpr _1887_recursiveGen;
            DCOMP._IOwnership _1888___v169;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1889_recIdents;
            RAST._IExpr _out398;
            DCOMP._IOwnership _out399;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out400;
            (this).GenExpr(_1886_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out398, out _out399, out _out400);
            _1887_recursiveGen = _out398;
            _1888___v169 = _out399;
            _1889_recIdents = _out400;
            RAST._IExpr _1890_lengthGen;
            DCOMP._IOwnership _1891___v170;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1892_lengthIdents;
            RAST._IExpr _out401;
            DCOMP._IOwnership _out402;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
            (this).GenExpr(_1885_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out401, out _out402, out _out403);
            _1890_lengthGen = _out401;
            _1891___v170 = _out402;
            _1892_lengthIdents = _out403;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1887_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1890_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1889_recIdents, _1892_lengthIdents);
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
          Dafny.ISequence<DAST._IExpression> _1893_exprs = _source95.dtor_elements;
          DAST._IType _1894_typ = _source95.dtor_typ;
          unmatched95 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1895_genTpe;
            RAST._IType _out406;
            _out406 = (this).GenType(_1894_typ, DCOMP.GenTypeContext.@default());
            _1895_genTpe = _out406;
            BigInteger _1896_i;
            _1896_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1897_args;
            _1897_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1896_i) < (new BigInteger((_1893_exprs).Count))) {
              RAST._IExpr _1898_recursiveGen;
              DCOMP._IOwnership _1899___v171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1900_recIdents;
              RAST._IExpr _out407;
              DCOMP._IOwnership _out408;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
              (this).GenExpr((_1893_exprs).Select(_1896_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out407, out _out408, out _out409);
              _1898_recursiveGen = _out407;
              _1899___v171 = _out408;
              _1900_recIdents = _out409;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1900_recIdents);
              _1897_args = Dafny.Sequence<RAST._IExpr>.Concat(_1897_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1898_recursiveGen));
              _1896_i = (_1896_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_1897_args);
            if ((new BigInteger((_1897_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1895_genTpe));
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
          Dafny.ISequence<DAST._IExpression> _1901_exprs = _source95.dtor_elements;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1902_generatedValues;
            _1902_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1903_i;
            _1903_i = BigInteger.Zero;
            while ((_1903_i) < (new BigInteger((_1901_exprs).Count))) {
              RAST._IExpr _1904_recursiveGen;
              DCOMP._IOwnership _1905___v172;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1906_recIdents;
              RAST._IExpr _out412;
              DCOMP._IOwnership _out413;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out414;
              (this).GenExpr((_1901_exprs).Select(_1903_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out412, out _out413, out _out414);
              _1904_recursiveGen = _out412;
              _1905___v172 = _out413;
              _1906_recIdents = _out414;
              _1902_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1902_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1904_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1906_recIdents);
              _1903_i = (_1903_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_1902_generatedValues);
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
          Dafny.ISequence<DAST._IExpression> _1907_exprs = _source95.dtor_elements;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1908_generatedValues;
            _1908_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1909_i;
            _1909_i = BigInteger.Zero;
            while ((_1909_i) < (new BigInteger((_1907_exprs).Count))) {
              RAST._IExpr _1910_recursiveGen;
              DCOMP._IOwnership _1911___v173;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1912_recIdents;
              RAST._IExpr _out417;
              DCOMP._IOwnership _out418;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out419;
              (this).GenExpr((_1907_exprs).Select(_1909_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out417, out _out418, out _out419);
              _1910_recursiveGen = _out417;
              _1911___v173 = _out418;
              _1912_recIdents = _out419;
              _1908_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1908_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1910_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1912_recIdents);
              _1909_i = (_1909_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_1908_generatedValues);
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
          DAST._IExpression _1913_expr = _source95.dtor_ToMultiset_a0;
          unmatched95 = false;
          {
            RAST._IExpr _1914_recursiveGen;
            DCOMP._IOwnership _1915___v174;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1916_recIdents;
            RAST._IExpr _out422;
            DCOMP._IOwnership _out423;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out424;
            (this).GenExpr(_1913_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out422, out _out423, out _out424);
            _1914_recursiveGen = _out422;
            _1915___v174 = _out423;
            _1916_recIdents = _out424;
            r = ((_1914_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _1916_recIdents;
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
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1917_mapElems = _source95.dtor_mapElems;
          unmatched95 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1918_generatedValues;
            _1918_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1919_i;
            _1919_i = BigInteger.Zero;
            while ((_1919_i) < (new BigInteger((_1917_mapElems).Count))) {
              RAST._IExpr _1920_recursiveGenKey;
              DCOMP._IOwnership _1921___v175;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1922_recIdentsKey;
              RAST._IExpr _out427;
              DCOMP._IOwnership _out428;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out429;
              (this).GenExpr(((_1917_mapElems).Select(_1919_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out427, out _out428, out _out429);
              _1920_recursiveGenKey = _out427;
              _1921___v175 = _out428;
              _1922_recIdentsKey = _out429;
              RAST._IExpr _1923_recursiveGenValue;
              DCOMP._IOwnership _1924___v176;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1925_recIdentsValue;
              RAST._IExpr _out430;
              DCOMP._IOwnership _out431;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out432;
              (this).GenExpr(((_1917_mapElems).Select(_1919_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out430, out _out431, out _out432);
              _1923_recursiveGenValue = _out430;
              _1924___v176 = _out431;
              _1925_recIdentsValue = _out432;
              _1918_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1918_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1920_recursiveGenKey, _1923_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1922_recIdentsKey), _1925_recIdentsValue);
              _1919_i = (_1919_i) + (BigInteger.One);
            }
            _1919_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1926_arguments;
            _1926_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1919_i) < (new BigInteger((_1918_generatedValues).Count))) {
              RAST._IExpr _1927_genKey;
              _1927_genKey = ((_1918_generatedValues).Select(_1919_i)).dtor__0;
              RAST._IExpr _1928_genValue;
              _1928_genValue = ((_1918_generatedValues).Select(_1919_i)).dtor__1;
              _1926_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1926_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1927_genKey, _1928_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _1919_i = (_1919_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_1926_arguments);
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
          DAST._IExpression _1929_expr = _source95.dtor_expr;
          DAST._IExpression _1930_index = _source95.dtor_indexExpr;
          DAST._IExpression _1931_value = _source95.dtor_value;
          unmatched95 = false;
          {
            RAST._IExpr _1932_exprR;
            DCOMP._IOwnership _1933___v177;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1934_exprIdents;
            RAST._IExpr _out435;
            DCOMP._IOwnership _out436;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out437;
            (this).GenExpr(_1929_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out435, out _out436, out _out437);
            _1932_exprR = _out435;
            _1933___v177 = _out436;
            _1934_exprIdents = _out437;
            RAST._IExpr _1935_indexR;
            DCOMP._IOwnership _1936_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1937_indexIdents;
            RAST._IExpr _out438;
            DCOMP._IOwnership _out439;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out440;
            (this).GenExpr(_1930_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out438, out _out439, out _out440);
            _1935_indexR = _out438;
            _1936_indexOwnership = _out439;
            _1937_indexIdents = _out440;
            RAST._IExpr _1938_valueR;
            DCOMP._IOwnership _1939_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1940_valueIdents;
            RAST._IExpr _out441;
            DCOMP._IOwnership _out442;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out443;
            (this).GenExpr(_1931_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out441, out _out442, out _out443);
            _1938_valueR = _out441;
            _1939_valueOwnership = _out442;
            _1940_valueIdents = _out443;
            r = ((_1932_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1935_indexR, _1938_valueR));
            RAST._IExpr _out444;
            DCOMP._IOwnership _out445;
            (this).FromOwned(r, expectedOwnership, out _out444, out _out445);
            r = _out444;
            resultingOwnership = _out445;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1934_exprIdents, _1937_indexIdents), _1940_valueIdents);
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_MapUpdate) {
          DAST._IExpression _1941_expr = _source95.dtor_expr;
          DAST._IExpression _1942_index = _source95.dtor_indexExpr;
          DAST._IExpression _1943_value = _source95.dtor_value;
          unmatched95 = false;
          {
            RAST._IExpr _1944_exprR;
            DCOMP._IOwnership _1945___v178;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1946_exprIdents;
            RAST._IExpr _out446;
            DCOMP._IOwnership _out447;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out448;
            (this).GenExpr(_1941_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out446, out _out447, out _out448);
            _1944_exprR = _out446;
            _1945___v178 = _out447;
            _1946_exprIdents = _out448;
            RAST._IExpr _1947_indexR;
            DCOMP._IOwnership _1948_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1949_indexIdents;
            RAST._IExpr _out449;
            DCOMP._IOwnership _out450;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
            (this).GenExpr(_1942_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out449, out _out450, out _out451);
            _1947_indexR = _out449;
            _1948_indexOwnership = _out450;
            _1949_indexIdents = _out451;
            RAST._IExpr _1950_valueR;
            DCOMP._IOwnership _1951_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1952_valueIdents;
            RAST._IExpr _out452;
            DCOMP._IOwnership _out453;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out454;
            (this).GenExpr(_1943_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out452, out _out453, out _out454);
            _1950_valueR = _out452;
            _1951_valueOwnership = _out453;
            _1952_valueIdents = _out454;
            r = ((_1944_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1947_indexR, _1950_valueR));
            RAST._IExpr _out455;
            DCOMP._IOwnership _out456;
            (this).FromOwned(r, expectedOwnership, out _out455, out _out456);
            r = _out455;
            resultingOwnership = _out456;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1946_exprIdents, _1949_indexIdents), _1952_valueIdents);
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
                Dafny.ISequence<Dafny.Rune> _1953_id = _source96.dtor_rSelfName;
                DAST._IType _1954_dafnyType = _source96.dtor_dafnyType;
                unmatched96 = false;
                {
                  RAST._IExpr _out457;
                  DCOMP._IOwnership _out458;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out459;
                  (this).GenIdent(_1953_id, selfIdent, env, expectedOwnership, out _out457, out _out458, out _out459);
                  r = _out457;
                  resultingOwnership = _out458;
                  readIdents = _out459;
                }
              }
            }
            if (unmatched96) {
              DCOMP._ISelfInfo _1955_None = _source96;
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
          DAST._IExpression _1956_cond = _source95.dtor_cond;
          DAST._IExpression _1957_t = _source95.dtor_thn;
          DAST._IExpression _1958_f = _source95.dtor_els;
          unmatched95 = false;
          {
            RAST._IExpr _1959_cond;
            DCOMP._IOwnership _1960___v179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1961_recIdentsCond;
            RAST._IExpr _out462;
            DCOMP._IOwnership _out463;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out464;
            (this).GenExpr(_1956_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out462, out _out463, out _out464);
            _1959_cond = _out462;
            _1960___v179 = _out463;
            _1961_recIdentsCond = _out464;
            RAST._IExpr _1962_fExpr;
            DCOMP._IOwnership _1963_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1964_recIdentsF;
            RAST._IExpr _out465;
            DCOMP._IOwnership _out466;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out467;
            (this).GenExpr(_1958_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out465, out _out466, out _out467);
            _1962_fExpr = _out465;
            _1963_fOwned = _out466;
            _1964_recIdentsF = _out467;
            RAST._IExpr _1965_tExpr;
            DCOMP._IOwnership _1966___v180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1967_recIdentsT;
            RAST._IExpr _out468;
            DCOMP._IOwnership _out469;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out470;
            (this).GenExpr(_1957_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out468, out _out469, out _out470);
            _1965_tExpr = _out468;
            _1966___v180 = _out469;
            _1967_recIdentsT = _out470;
            r = RAST.Expr.create_IfExpr(_1959_cond, _1965_tExpr, _1962_fExpr);
            RAST._IExpr _out471;
            DCOMP._IOwnership _out472;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out471, out _out472);
            r = _out471;
            resultingOwnership = _out472;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1961_recIdentsCond, _1967_recIdentsT), _1964_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source95.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _1968_e = _source95.dtor_expr;
            DAST.Format._IUnaryOpFormat _1969_format = _source95.dtor_format1;
            unmatched95 = false;
            {
              RAST._IExpr _1970_recursiveGen;
              DCOMP._IOwnership _1971___v181;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1972_recIdents;
              RAST._IExpr _out473;
              DCOMP._IOwnership _out474;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out475;
              (this).GenExpr(_1968_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out473, out _out474, out _out475);
              _1970_recursiveGen = _out473;
              _1971___v181 = _out474;
              _1972_recIdents = _out475;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _1970_recursiveGen, _1969_format);
              RAST._IExpr _out476;
              DCOMP._IOwnership _out477;
              (this).FromOwned(r, expectedOwnership, out _out476, out _out477);
              r = _out476;
              resultingOwnership = _out477;
              readIdents = _1972_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source95.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _1973_e = _source95.dtor_expr;
            DAST.Format._IUnaryOpFormat _1974_format = _source95.dtor_format1;
            unmatched95 = false;
            {
              RAST._IExpr _1975_recursiveGen;
              DCOMP._IOwnership _1976___v182;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1977_recIdents;
              RAST._IExpr _out478;
              DCOMP._IOwnership _out479;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out480;
              (this).GenExpr(_1973_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out478, out _out479, out _out480);
              _1975_recursiveGen = _out478;
              _1976___v182 = _out479;
              _1977_recIdents = _out480;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _1975_recursiveGen, _1974_format);
              RAST._IExpr _out481;
              DCOMP._IOwnership _out482;
              (this).FromOwned(r, expectedOwnership, out _out481, out _out482);
              r = _out481;
              resultingOwnership = _out482;
              readIdents = _1977_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source95.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _1978_e = _source95.dtor_expr;
            DAST.Format._IUnaryOpFormat _1979_format = _source95.dtor_format1;
            unmatched95 = false;
            {
              RAST._IExpr _1980_recursiveGen;
              DCOMP._IOwnership _1981_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1982_recIdents;
              RAST._IExpr _out483;
              DCOMP._IOwnership _out484;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out485;
              (this).GenExpr(_1978_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out483, out _out484, out _out485);
              _1980_recursiveGen = _out483;
              _1981_recOwned = _out484;
              _1982_recIdents = _out485;
              r = ((_1980_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out486;
              DCOMP._IOwnership _out487;
              (this).FromOwned(r, expectedOwnership, out _out486, out _out487);
              r = _out486;
              resultingOwnership = _out487;
              readIdents = _1982_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_BinOp) {
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
          DAST._IExpression _1983_expr = _source95.dtor_expr;
          DAST._IType _1984_exprType = _source95.dtor_exprType;
          BigInteger _1985_dim = _source95.dtor_dim;
          bool _1986_native = _source95.dtor_native;
          unmatched95 = false;
          {
            RAST._IExpr _1987_recursiveGen;
            DCOMP._IOwnership _1988___v187;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1989_recIdents;
            RAST._IExpr _out491;
            DCOMP._IOwnership _out492;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out493;
            (this).GenExpr(_1983_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out491, out _out492, out _out493);
            _1987_recursiveGen = _out491;
            _1988___v187 = _out492;
            _1989_recIdents = _out493;
            RAST._IType _1990_arrayType;
            RAST._IType _out494;
            _out494 = (this).GenType(_1984_exprType, DCOMP.GenTypeContext.@default());
            _1990_arrayType = _out494;
            if (!((_1990_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _1991_msg;
              _1991_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_1990_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1991_msg);
              r = RAST.Expr.create_RawExpr(_1991_msg);
            } else {
              RAST._IType _1992_underlying;
              _1992_underlying = (_1990_arrayType).ObjectOrPointerUnderlying();
              if (((_1985_dim).Sign == 0) && ((_1992_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_1987_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_1985_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_1987_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = (((this).read__macro).Apply1(_1987_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Length"), Std.Strings.__default.OfNat(_1985_dim)));
                }
              }
              if (!(_1986_native)) {
                r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(r);
              }
            }
            RAST._IExpr _out495;
            DCOMP._IOwnership _out496;
            (this).FromOwned(r, expectedOwnership, out _out495, out _out496);
            r = _out495;
            resultingOwnership = _out496;
            readIdents = _1989_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_MapKeys) {
          DAST._IExpression _1993_expr = _source95.dtor_expr;
          unmatched95 = false;
          {
            RAST._IExpr _1994_recursiveGen;
            DCOMP._IOwnership _1995___v188;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1996_recIdents;
            RAST._IExpr _out497;
            DCOMP._IOwnership _out498;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out499;
            (this).GenExpr(_1993_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out497, out _out498, out _out499);
            _1994_recursiveGen = _out497;
            _1995___v188 = _out498;
            _1996_recIdents = _out499;
            readIdents = _1996_recIdents;
            r = ((_1994_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
          DAST._IExpression _1997_expr = _source95.dtor_expr;
          unmatched95 = false;
          {
            RAST._IExpr _1998_recursiveGen;
            DCOMP._IOwnership _1999___v189;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2000_recIdents;
            RAST._IExpr _out502;
            DCOMP._IOwnership _out503;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out504;
            (this).GenExpr(_1997_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out502, out _out503, out _out504);
            _1998_recursiveGen = _out502;
            _1999___v189 = _out503;
            _2000_recIdents = _out504;
            readIdents = _2000_recIdents;
            r = ((_1998_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
          DAST._IExpression _2001_on = _source95.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2002_field = _source95.dtor_field;
          bool _2003_isDatatype = _source95.dtor_onDatatype;
          bool _2004_isStatic = _source95.dtor_isStatic;
          BigInteger _2005_arity = _source95.dtor_arity;
          unmatched95 = false;
          {
            RAST._IExpr _2006_onExpr;
            DCOMP._IOwnership _2007_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2008_recIdents;
            RAST._IExpr _out507;
            DCOMP._IOwnership _out508;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out509;
            (this).GenExpr(_2001_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out507, out _out508, out _out509);
            _2006_onExpr = _out507;
            _2007_onOwned = _out508;
            _2008_recIdents = _out509;
            Dafny.ISequence<Dafny.Rune> _2009_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _2010_onString;
            _2010_onString = (_2006_onExpr)._ToString(DCOMP.__default.IND);
            if (_2004_isStatic) {
              _2009_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2010_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_2002_field));
            } else {
              _2009_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _2009_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2009_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2010_onString), ((object.Equals(_2007_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _2011_args;
              _2011_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _2012_i;
              _2012_i = BigInteger.Zero;
              while ((_2012_i) < (_2005_arity)) {
                if ((_2012_i).Sign == 1) {
                  _2011_args = Dafny.Sequence<Dafny.Rune>.Concat(_2011_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _2011_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2011_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_2012_i));
                _2012_i = (_2012_i) + (BigInteger.One);
              }
              _2009_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2009_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2011_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _2009_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2009_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_2002_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2011_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _2009_s = Dafny.Sequence<Dafny.Rune>.Concat(_2009_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _2009_s = Dafny.Sequence<Dafny.Rune>.Concat(_2009_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _2013_typeShape;
            _2013_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _2014_i;
            _2014_i = BigInteger.Zero;
            while ((_2014_i) < (_2005_arity)) {
              if ((_2014_i).Sign == 1) {
                _2013_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2013_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2013_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2013_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _2014_i = (_2014_i) + (BigInteger.One);
            }
            _2013_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2013_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _2009_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _2009_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _2013_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_2009_s);
            RAST._IExpr _out510;
            DCOMP._IOwnership _out511;
            (this).FromOwned(r, expectedOwnership, out _out510, out _out511);
            r = _out510;
            resultingOwnership = _out511;
            readIdents = _2008_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Select) {
          DAST._IExpression expr0 = _source95.dtor_expr;
          if (expr0.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2015_c = expr0.dtor_Companion_a0;
            Dafny.ISequence<DAST._IType> _2016_typeArgs = expr0.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _2017_field = _source95.dtor_field;
            bool _2018_isConstant = _source95.dtor_isConstant;
            bool _2019_isDatatype = _source95.dtor_onDatatype;
            DAST._IType _2020_fieldType = _source95.dtor_fieldType;
            unmatched95 = false;
            {
              RAST._IExpr _2021_onExpr;
              DCOMP._IOwnership _2022_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2023_recIdents;
              RAST._IExpr _out512;
              DCOMP._IOwnership _out513;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out514;
              (this).GenExpr(DAST.Expression.create_Companion(_2015_c, _2016_typeArgs), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out512, out _out513, out _out514);
              _2021_onExpr = _out512;
              _2022_onOwned = _out513;
              _2023_recIdents = _out514;
              r = ((_2021_onExpr).MSel(DCOMP.__default.escapeName(_2017_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out515;
              DCOMP._IOwnership _out516;
              (this).FromOwned(r, expectedOwnership, out _out515, out _out516);
              r = _out515;
              resultingOwnership = _out516;
              readIdents = _2023_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Select) {
          DAST._IExpression _2024_on = _source95.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2025_field = _source95.dtor_field;
          bool _2026_isConstant = _source95.dtor_isConstant;
          bool _2027_isDatatype = _source95.dtor_onDatatype;
          DAST._IType _2028_fieldType = _source95.dtor_fieldType;
          unmatched95 = false;
          {
            if (_2027_isDatatype) {
              RAST._IExpr _2029_onExpr;
              DCOMP._IOwnership _2030_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2031_recIdents;
              RAST._IExpr _out517;
              DCOMP._IOwnership _out518;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out519;
              (this).GenExpr(_2024_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out517, out _out518, out _out519);
              _2029_onExpr = _out517;
              _2030_onOwned = _out518;
              _2031_recIdents = _out519;
              r = ((_2029_onExpr).Sel(DCOMP.__default.escapeName(_2025_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _2032_typ;
              RAST._IType _out520;
              _out520 = (this).GenType(_2028_fieldType, DCOMP.GenTypeContext.@default());
              _2032_typ = _out520;
              RAST._IExpr _out521;
              DCOMP._IOwnership _out522;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out521, out _out522);
              r = _out521;
              resultingOwnership = _out522;
              readIdents = _2031_recIdents;
            } else {
              RAST._IExpr _2033_onExpr;
              DCOMP._IOwnership _2034_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2035_recIdents;
              RAST._IExpr _out523;
              DCOMP._IOwnership _out524;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
              (this).GenExpr(_2024_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out523, out _out524, out _out525);
              _2033_onExpr = _out523;
              _2034_onOwned = _out524;
              _2035_recIdents = _out525;
              r = _2033_onExpr;
              if (!object.Equals(_2033_onExpr, RAST.__default.self)) {
                RAST._IExpr _source97 = _2033_onExpr;
                bool unmatched97 = true;
                if (unmatched97) {
                  if (_source97.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> op15 = _source97.dtor_op1;
                    if (object.Equals(op15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                      RAST._IExpr underlying5 = _source97.dtor_underlying;
                      if (underlying5.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name15 = underlying5.dtor_name;
                        if (object.Equals(name15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                          unmatched97 = false;
                          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
                        }
                      }
                    }
                  }
                }
                if (unmatched97) {
                  unmatched97 = false;
                }
                if (((this).ObjectType).is_RcMut) {
                  r = (r).Clone();
                }
                r = ((this).read__macro).Apply1(r);
              }
              r = (r).Sel(DCOMP.__default.escapeName(_2025_field));
              if (_2026_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out526;
              DCOMP._IOwnership _out527;
              (this).FromOwned(r, expectedOwnership, out _out526, out _out527);
              r = _out526;
              resultingOwnership = _out527;
              readIdents = _2035_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Index) {
          DAST._IExpression _2036_on = _source95.dtor_expr;
          DAST._ICollKind _2037_collKind = _source95.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2038_indices = _source95.dtor_indices;
          unmatched95 = false;
          {
            RAST._IExpr _2039_onExpr;
            DCOMP._IOwnership _2040_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2041_recIdents;
            RAST._IExpr _out528;
            DCOMP._IOwnership _out529;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out530;
            (this).GenExpr(_2036_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out528, out _out529, out _out530);
            _2039_onExpr = _out528;
            _2040_onOwned = _out529;
            _2041_recIdents = _out530;
            readIdents = _2041_recIdents;
            r = _2039_onExpr;
            BigInteger _2042_i;
            _2042_i = BigInteger.Zero;
            while ((_2042_i) < (new BigInteger((_2038_indices).Count))) {
              if (object.Equals(_2037_collKind, DAST.CollKind.create_Array())) {
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              RAST._IExpr _2043_idx;
              DCOMP._IOwnership _2044_idxOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2045_recIdentsIdx;
              RAST._IExpr _out531;
              DCOMP._IOwnership _out532;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out533;
              (this).GenExpr((_2038_indices).Select(_2042_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out531, out _out532, out _out533);
              _2043_idx = _out531;
              _2044_idxOwned = _out532;
              _2045_recIdentsIdx = _out533;
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_2043_idx);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2045_recIdentsIdx);
              _2042_i = (_2042_i) + (BigInteger.One);
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
          DAST._IExpression _2046_on = _source95.dtor_expr;
          bool _2047_isArray = _source95.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _2048_low = _source95.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _2049_high = _source95.dtor_high;
          unmatched95 = false;
          {
            RAST._IExpr _2050_onExpr;
            DCOMP._IOwnership _2051_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2052_recIdents;
            RAST._IExpr _out536;
            DCOMP._IOwnership _out537;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out538;
            (this).GenExpr(_2046_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out536, out _out537, out _out538);
            _2050_onExpr = _out536;
            _2051_onOwned = _out537;
            _2052_recIdents = _out538;
            readIdents = _2052_recIdents;
            Dafny.ISequence<Dafny.Rune> _2053_methodName;
            _2053_methodName = (((_2048_low).is_Some) ? ((((_2049_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_2049_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _2054_arguments;
            _2054_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source98 = _2048_low;
            bool unmatched98 = true;
            if (unmatched98) {
              if (_source98.is_Some) {
                DAST._IExpression _2055_l = _source98.dtor_value;
                unmatched98 = false;
                {
                  RAST._IExpr _2056_lExpr;
                  DCOMP._IOwnership _2057___v192;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2058_recIdentsL;
                  RAST._IExpr _out539;
                  DCOMP._IOwnership _out540;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
                  (this).GenExpr(_2055_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out539, out _out540, out _out541);
                  _2056_lExpr = _out539;
                  _2057___v192 = _out540;
                  _2058_recIdentsL = _out541;
                  _2054_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2054_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2056_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2058_recIdentsL);
                }
              }
            }
            if (unmatched98) {
              unmatched98 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source99 = _2049_high;
            bool unmatched99 = true;
            if (unmatched99) {
              if (_source99.is_Some) {
                DAST._IExpression _2059_h = _source99.dtor_value;
                unmatched99 = false;
                {
                  RAST._IExpr _2060_hExpr;
                  DCOMP._IOwnership _2061___v193;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2062_recIdentsH;
                  RAST._IExpr _out542;
                  DCOMP._IOwnership _out543;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out544;
                  (this).GenExpr(_2059_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out542, out _out543, out _out544);
                  _2060_hExpr = _out542;
                  _2061___v193 = _out543;
                  _2062_recIdentsH = _out544;
                  _2054_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2054_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2060_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2062_recIdentsH);
                }
              }
            }
            if (unmatched99) {
              unmatched99 = false;
            }
            r = _2050_onExpr;
            if (_2047_isArray) {
              if (!(_2053_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _2053_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2053_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _2053_methodName))).Apply(_2054_arguments);
            } else {
              if (!(_2053_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_2053_methodName)).Apply(_2054_arguments);
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
          DAST._IExpression _2063_on = _source95.dtor_expr;
          BigInteger _2064_idx = _source95.dtor_index;
          DAST._IType _2065_fieldType = _source95.dtor_fieldType;
          unmatched95 = false;
          {
            RAST._IExpr _2066_onExpr;
            DCOMP._IOwnership _2067_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2068_recIdents;
            RAST._IExpr _out547;
            DCOMP._IOwnership _out548;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out549;
            (this).GenExpr(_2063_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out547, out _out548, out _out549);
            _2066_onExpr = _out547;
            _2067_onOwnership = _out548;
            _2068_recIdents = _out549;
            Dafny.ISequence<Dafny.Rune> _2069_selName;
            _2069_selName = Std.Strings.__default.OfNat(_2064_idx);
            DAST._IType _source100 = _2065_fieldType;
            bool unmatched100 = true;
            if (unmatched100) {
              if (_source100.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2070_tps = _source100.dtor_Tuple_a0;
                unmatched100 = false;
                if (((_2065_fieldType).is_Tuple) && ((new BigInteger((_2070_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _2069_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2069_selName);
                }
              }
            }
            if (unmatched100) {
              unmatched100 = false;
            }
            r = ((_2066_onExpr).Sel(_2069_selName)).Clone();
            RAST._IExpr _out550;
            DCOMP._IOwnership _out551;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out550, out _out551);
            r = _out550;
            resultingOwnership = _out551;
            readIdents = _2068_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Call) {
          DAST._IExpression _2071_on = _source95.dtor_on;
          DAST._ICallName _2072_name = _source95.dtor_callName;
          Dafny.ISequence<DAST._IType> _2073_typeArgs = _source95.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2074_args = _source95.dtor_args;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2075_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2076_recIdents;
            Dafny.ISequence<RAST._IType> _2077_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _2078_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out552;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out553;
            Dafny.ISequence<RAST._IType> _out554;
            Std.Wrappers._IOption<DAST._IResolvedType> _out555;
            (this).GenArgs(selfIdent, _2072_name, _2073_typeArgs, _2074_args, env, out _out552, out _out553, out _out554, out _out555);
            _2075_argExprs = _out552;
            _2076_recIdents = _out553;
            _2077_typeExprs = _out554;
            _2078_fullNameQualifier = _out555;
            readIdents = _2076_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source101 = _2078_fullNameQualifier;
            bool unmatched101 = true;
            if (unmatched101) {
              if (_source101.is_Some) {
                DAST._IResolvedType value11 = _source101.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2079_path = value11.dtor_path;
                Dafny.ISequence<DAST._IType> _2080_onTypeArgs = value11.dtor_typeArgs;
                DAST._IResolvedTypeBase _2081_base = value11.dtor_kind;
                unmatched101 = false;
                RAST._IExpr _2082_fullPath;
                RAST._IExpr _out556;
                _out556 = DCOMP.COMP.GenPathExpr(_2079_path);
                _2082_fullPath = _out556;
                Dafny.ISequence<RAST._IType> _2083_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out557;
                _out557 = (this).GenTypeArgs(_2080_onTypeArgs, DCOMP.GenTypeContext.@default());
                _2083_onTypeExprs = _out557;
                RAST._IExpr _2084_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _2085_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2086_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_2081_base).is_Trait) || ((_2081_base).is_Class)) {
                  RAST._IExpr _out558;
                  DCOMP._IOwnership _out559;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out560;
                  (this).GenExpr(_2071_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out558, out _out559, out _out560);
                  _2084_onExpr = _out558;
                  _2085_recOwnership = _out559;
                  _2086_recIdents = _out560;
                  _2084_onExpr = ((this).read__macro).Apply1(_2084_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2086_recIdents);
                } else {
                  RAST._IExpr _out561;
                  DCOMP._IOwnership _out562;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out563;
                  (this).GenExpr(_2071_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out561, out _out562, out _out563);
                  _2084_onExpr = _out561;
                  _2085_recOwnership = _out562;
                  _2086_recIdents = _out563;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2086_recIdents);
                }
                r = ((((_2082_fullPath).ApplyType(_2083_onTypeExprs)).MSel(DCOMP.__default.escapeName((_2072_name).dtor_name))).ApplyType(_2077_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_2084_onExpr), _2075_argExprs));
                RAST._IExpr _out564;
                DCOMP._IOwnership _out565;
                (this).FromOwned(r, expectedOwnership, out _out564, out _out565);
                r = _out564;
                resultingOwnership = _out565;
              }
            }
            if (unmatched101) {
              unmatched101 = false;
              RAST._IExpr _2087_onExpr;
              DCOMP._IOwnership _2088___v199;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2089_recIdents;
              RAST._IExpr _out566;
              DCOMP._IOwnership _out567;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out568;
              (this).GenExpr(_2071_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out566, out _out567, out _out568);
              _2087_onExpr = _out566;
              _2088___v199 = _out567;
              _2089_recIdents = _out568;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2089_recIdents);
              Dafny.ISequence<Dafny.Rune> _2090_renderedName;
              _2090_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
                DAST._ICallName _source102 = _2072_name;
                bool unmatched102 = true;
                if (unmatched102) {
                  if (_source102.is_CallName) {
                    Dafny.ISequence<Dafny.Rune> _2091_ident = _source102.dtor_name;
                    unmatched102 = false;
                    return DCOMP.__default.escapeName(_2091_ident);
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
              DAST._IExpression _source103 = _2071_on;
              bool unmatched103 = true;
              if (unmatched103) {
                if (_source103.is_Companion) {
                  unmatched103 = false;
                  {
                    _2087_onExpr = (_2087_onExpr).MSel(_2090_renderedName);
                  }
                }
              }
              if (unmatched103) {
                unmatched103 = false;
                {
                  if (!object.Equals(_2087_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source104 = _2072_name;
                    bool unmatched104 = true;
                    if (unmatched104) {
                      if (_source104.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType2 = _source104.dtor_onType;
                        if (onType2.is_Some) {
                          DAST._IType _2092_tpe = onType2.dtor_value;
                          unmatched104 = false;
                          RAST._IType _2093_typ;
                          RAST._IType _out569;
                          _out569 = (this).GenType(_2092_tpe, DCOMP.GenTypeContext.@default());
                          _2093_typ = _out569;
                          if ((_2093_typ).IsObjectOrPointer()) {
                            _2087_onExpr = ((this).read__macro).Apply1(_2087_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched104) {
                      unmatched104 = false;
                    }
                  }
                  _2087_onExpr = (_2087_onExpr).Sel(_2090_renderedName);
                }
              }
              r = ((_2087_onExpr).ApplyType(_2077_typeExprs)).Apply(_2075_argExprs);
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
          Dafny.ISequence<DAST._IFormal> _2094_paramsDafny = _source95.dtor_params;
          DAST._IType _2095_retType = _source95.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2096_body = _source95.dtor_body;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IFormal> _2097_params;
            Dafny.ISequence<RAST._IFormal> _out572;
            _out572 = (this).GenParams(_2094_paramsDafny);
            _2097_params = _out572;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2098_paramNames;
            _2098_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2099_paramTypesMap;
            _2099_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi45 = new BigInteger((_2097_params).Count);
            for (BigInteger _2100_i = BigInteger.Zero; _2100_i < _hi45; _2100_i++) {
              Dafny.ISequence<Dafny.Rune> _2101_name;
              _2101_name = ((_2097_params).Select(_2100_i)).dtor_name;
              _2098_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2098_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2101_name));
              _2099_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2099_paramTypesMap, _2101_name, ((_2097_params).Select(_2100_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _2102_subEnv;
            _2102_subEnv = ((env).ToOwned()).merge(DCOMP.Environment.create(_2098_paramNames, _2099_paramTypesMap));
            RAST._IExpr _2103_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2104_recIdents;
            DCOMP._IEnvironment _2105___v210;
            RAST._IExpr _out573;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out574;
            DCOMP._IEnvironment _out575;
            (this).GenStmts(_2096_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _2102_subEnv, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out573, out _out574, out _out575);
            _2103_recursiveGen = _out573;
            _2104_recIdents = _out574;
            _2105___v210 = _out575;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _2104_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2104_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_2106_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll7 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_7 in (_2106_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _2107_name = (Dafny.ISequence<Dafny.Rune>)_compr_7;
                if ((_2106_paramNames).Contains(_2107_name)) {
                  _coll7.Add(_2107_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll7);
            }))())(_2098_paramNames));
            RAST._IExpr _2108_allReadCloned;
            _2108_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_2104_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _2109_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_2104_recIdents).Elements) {
                _2109_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_2104_recIdents).Contains(_2109_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 4793)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_2109_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _2110_selfCloned;
                DCOMP._IOwnership _2111___v211;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2112___v212;
                RAST._IExpr _out576;
                DCOMP._IOwnership _out577;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out578;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out576, out _out577, out _out578);
                _2110_selfCloned = _out576;
                _2111___v211 = _out577;
                _2112___v212 = _out578;
                _2108_allReadCloned = (_2108_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2110_selfCloned)));
              } else if (!((_2098_paramNames).Contains(_2109_next))) {
                RAST._IExpr _2113_copy;
                _2113_copy = (RAST.Expr.create_Identifier(_2109_next)).Clone();
                _2108_allReadCloned = (_2108_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2109_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2113_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2109_next));
              }
              _2104_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2104_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2109_next));
            }
            RAST._IType _2114_retTypeGen;
            RAST._IType _out579;
            _out579 = (this).GenType(_2095_retType, DCOMP.GenTypeContext.InFn());
            _2114_retTypeGen = _out579;
            r = RAST.Expr.create_Block((_2108_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_2097_params, Std.Wrappers.Option<RAST._IType>.create_Some(_2114_retTypeGen), RAST.Expr.create_Block(_2103_recursiveGen)))));
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
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2115_values = _source95.dtor_values;
          DAST._IType _2116_retType = _source95.dtor_retType;
          DAST._IExpression _2117_expr = _source95.dtor_expr;
          unmatched95 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2118_paramNames;
            _2118_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2119_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out582;
            _out582 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2120_value) => {
              return (_2120_value).dtor__0;
            })), _2115_values));
            _2119_paramFormals = _out582;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2121_paramTypes;
            _2121_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2122_paramNamesSet;
            _2122_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi46 = new BigInteger((_2115_values).Count);
            for (BigInteger _2123_i = BigInteger.Zero; _2123_i < _hi46; _2123_i++) {
              Dafny.ISequence<Dafny.Rune> _2124_name;
              _2124_name = (((_2115_values).Select(_2123_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2125_rName;
              _2125_rName = DCOMP.__default.escapeName(_2124_name);
              _2118_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2118_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2125_rName));
              _2121_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2121_paramTypes, _2125_rName, ((_2119_paramFormals).Select(_2123_i)).dtor_tpe);
              _2122_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2122_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2125_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi47 = new BigInteger((_2115_values).Count);
            for (BigInteger _2126_i = BigInteger.Zero; _2126_i < _hi47; _2126_i++) {
              RAST._IType _2127_typeGen;
              RAST._IType _out583;
              _out583 = (this).GenType((((_2115_values).Select(_2126_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.InFn());
              _2127_typeGen = _out583;
              RAST._IExpr _2128_valueGen;
              DCOMP._IOwnership _2129___v213;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2130_recIdents;
              RAST._IExpr _out584;
              DCOMP._IOwnership _out585;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out586;
              (this).GenExpr(((_2115_values).Select(_2126_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out584, out _out585, out _out586);
              _2128_valueGen = _out584;
              _2129___v213 = _out585;
              _2130_recIdents = _out586;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_2115_values).Select(_2126_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2127_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2128_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2130_recIdents);
            }
            DCOMP._IEnvironment _2131_newEnv;
            _2131_newEnv = DCOMP.Environment.create(_2118_paramNames, _2121_paramTypes);
            RAST._IExpr _2132_recGen;
            DCOMP._IOwnership _2133_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2134_recIdents;
            RAST._IExpr _out587;
            DCOMP._IOwnership _out588;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out589;
            (this).GenExpr(_2117_expr, selfIdent, _2131_newEnv, expectedOwnership, out _out587, out _out588, out _out589);
            _2132_recGen = _out587;
            _2133_recOwned = _out588;
            _2134_recIdents = _out589;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2134_recIdents, _2122_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2132_recGen));
            RAST._IExpr _out590;
            DCOMP._IOwnership _out591;
            (this).FromOwnership(r, _2133_recOwned, expectedOwnership, out _out590, out _out591);
            r = _out590;
            resultingOwnership = _out591;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2135_name = _source95.dtor_name;
          DAST._IType _2136_tpe = _source95.dtor_typ;
          DAST._IExpression _2137_value = _source95.dtor_value;
          DAST._IExpression _2138_iifeBody = _source95.dtor_iifeBody;
          unmatched95 = false;
          {
            RAST._IExpr _2139_valueGen;
            DCOMP._IOwnership _2140___v214;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2141_recIdents;
            RAST._IExpr _out592;
            DCOMP._IOwnership _out593;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out594;
            (this).GenExpr(_2137_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out592, out _out593, out _out594);
            _2139_valueGen = _out592;
            _2140___v214 = _out593;
            _2141_recIdents = _out594;
            readIdents = _2141_recIdents;
            RAST._IType _2142_valueTypeGen;
            RAST._IType _out595;
            _out595 = (this).GenType(_2136_tpe, DCOMP.GenTypeContext.InFn());
            _2142_valueTypeGen = _out595;
            RAST._IExpr _2143_bodyGen;
            DCOMP._IOwnership _2144___v215;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2145_bodyIdents;
            RAST._IExpr _out596;
            DCOMP._IOwnership _out597;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out598;
            (this).GenExpr(_2138_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out596, out _out597, out _out598);
            _2143_bodyGen = _out596;
            _2144___v215 = _out597;
            _2145_bodyIdents = _out598;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2145_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_2135_name)))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_2135_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_2142_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2139_valueGen))).Then(_2143_bodyGen));
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
          DAST._IExpression _2146_func = _source95.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2147_args = _source95.dtor_args;
          unmatched95 = false;
          {
            RAST._IExpr _2148_funcExpr;
            DCOMP._IOwnership _2149___v216;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2150_recIdents;
            RAST._IExpr _out601;
            DCOMP._IOwnership _out602;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out603;
            (this).GenExpr(_2146_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out601, out _out602, out _out603);
            _2148_funcExpr = _out601;
            _2149___v216 = _out602;
            _2150_recIdents = _out603;
            readIdents = _2150_recIdents;
            Dafny.ISequence<RAST._IExpr> _2151_rArgs;
            _2151_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi48 = new BigInteger((_2147_args).Count);
            for (BigInteger _2152_i = BigInteger.Zero; _2152_i < _hi48; _2152_i++) {
              RAST._IExpr _2153_argExpr;
              DCOMP._IOwnership _2154_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2155_argIdents;
              RAST._IExpr _out604;
              DCOMP._IOwnership _out605;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out606;
              (this).GenExpr((_2147_args).Select(_2152_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out604, out _out605, out _out606);
              _2153_argExpr = _out604;
              _2154_argOwned = _out605;
              _2155_argIdents = _out606;
              _2151_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2151_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2153_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2155_argIdents);
            }
            r = (_2148_funcExpr).Apply(_2151_rArgs);
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
          DAST._IExpression _2156_on = _source95.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2157_dType = _source95.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2158_variant = _source95.dtor_variant;
          unmatched95 = false;
          {
            RAST._IExpr _2159_exprGen;
            DCOMP._IOwnership _2160___v217;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2161_recIdents;
            RAST._IExpr _out609;
            DCOMP._IOwnership _out610;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out611;
            (this).GenExpr(_2156_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out609, out _out610, out _out611);
            _2159_exprGen = _out609;
            _2160___v217 = _out610;
            _2161_recIdents = _out611;
            RAST._IType _2162_dTypePath;
            RAST._IType _out612;
            _out612 = DCOMP.COMP.GenPath(_2157_dType);
            _2162_dTypePath = _out612;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2159_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_2162_dTypePath).MSel(DCOMP.__default.escapeName(_2158_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out613;
            DCOMP._IOwnership _out614;
            (this).FromOwned(r, expectedOwnership, out _out613, out _out614);
            r = _out613;
            resultingOwnership = _out614;
            readIdents = _2161_recIdents;
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
          DAST._IExpression _2163_of = _source95.dtor_of;
          unmatched95 = false;
          {
            RAST._IExpr _2164_exprGen;
            DCOMP._IOwnership _2165___v218;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2166_recIdents;
            RAST._IExpr _out617;
            DCOMP._IOwnership _out618;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out619;
            (this).GenExpr(_2163_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out617, out _out618, out _out619);
            _2164_exprGen = _out617;
            _2165___v218 = _out618;
            _2166_recIdents = _out619;
            r = ((_2164_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out620;
            DCOMP._IOwnership _out621;
            (this).FromOwned(r, expectedOwnership, out _out620, out _out621);
            r = _out620;
            resultingOwnership = _out621;
            readIdents = _2166_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_SeqBoundedPool) {
          DAST._IExpression _2167_of = _source95.dtor_of;
          bool _2168_includeDuplicates = _source95.dtor_includeDuplicates;
          unmatched95 = false;
          {
            RAST._IExpr _2169_exprGen;
            DCOMP._IOwnership _2170___v219;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2171_recIdents;
            RAST._IExpr _out622;
            DCOMP._IOwnership _out623;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out624;
            (this).GenExpr(_2167_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out622, out _out623, out _out624);
            _2169_exprGen = _out622;
            _2170___v219 = _out623;
            _2171_recIdents = _out624;
            r = ((_2169_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2168_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out625;
            DCOMP._IOwnership _out626;
            (this).FromOwned(r, expectedOwnership, out _out625, out _out626);
            r = _out625;
            resultingOwnership = _out626;
            readIdents = _2171_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_MapBoundedPool) {
          DAST._IExpression _2172_of = _source95.dtor_of;
          unmatched95 = false;
          {
            RAST._IExpr _2173_exprGen;
            DCOMP._IOwnership _2174___v220;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2175_recIdents;
            RAST._IExpr _out627;
            DCOMP._IOwnership _out628;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out629;
            (this).GenExpr(_2172_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out627, out _out628, out _out629);
            _2173_exprGen = _out627;
            _2174___v220 = _out628;
            _2175_recIdents = _out629;
            r = ((((_2173_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2175_recIdents;
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
          DAST._IExpression _2176_lo = _source95.dtor_lo;
          DAST._IExpression _2177_hi = _source95.dtor_hi;
          bool _2178_up = _source95.dtor_up;
          unmatched95 = false;
          {
            RAST._IExpr _2179_lo;
            DCOMP._IOwnership _2180___v221;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2181_recIdentsLo;
            RAST._IExpr _out632;
            DCOMP._IOwnership _out633;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out634;
            (this).GenExpr(_2176_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out632, out _out633, out _out634);
            _2179_lo = _out632;
            _2180___v221 = _out633;
            _2181_recIdentsLo = _out634;
            RAST._IExpr _2182_hi;
            DCOMP._IOwnership _2183___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2184_recIdentsHi;
            RAST._IExpr _out635;
            DCOMP._IOwnership _out636;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out637;
            (this).GenExpr(_2177_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out635, out _out636, out _out637);
            _2182_hi = _out635;
            _2183___v222 = _out636;
            _2184_recIdentsHi = _out637;
            if (_2178_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2179_lo, _2182_hi));
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2182_hi, _2179_lo));
            }
            RAST._IExpr _out638;
            DCOMP._IOwnership _out639;
            (this).FromOwned(r, expectedOwnership, out _out638, out _out639);
            r = _out638;
            resultingOwnership = _out639;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2181_recIdentsLo, _2184_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_UnboundedIntRange) {
          DAST._IExpression _2185_start = _source95.dtor_start;
          bool _2186_up = _source95.dtor_up;
          unmatched95 = false;
          {
            RAST._IExpr _2187_start;
            DCOMP._IOwnership _2188___v223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2189_recIdentStart;
            RAST._IExpr _out640;
            DCOMP._IOwnership _out641;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out642;
            (this).GenExpr(_2185_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out640, out _out641, out _out642);
            _2187_start = _out640;
            _2188___v223 = _out641;
            _2189_recIdentStart = _out642;
            if (_2186_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).Apply1(_2187_start);
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).Apply1(_2187_start);
            }
            RAST._IExpr _out643;
            DCOMP._IOwnership _out644;
            (this).FromOwned(r, expectedOwnership, out _out643, out _out644);
            r = _out643;
            resultingOwnership = _out644;
            readIdents = _2189_recIdentStart;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_MapBuilder) {
          DAST._IType _2190_keyType = _source95.dtor_keyType;
          DAST._IType _2191_valueType = _source95.dtor_valueType;
          unmatched95 = false;
          {
            RAST._IType _2192_kType;
            RAST._IType _out645;
            _out645 = (this).GenType(_2190_keyType, DCOMP.GenTypeContext.@default());
            _2192_kType = _out645;
            RAST._IType _2193_vType;
            RAST._IType _out646;
            _out646 = (this).GenType(_2191_valueType, DCOMP.GenTypeContext.@default());
            _2193_vType = _out646;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2192_kType, _2193_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
          DAST._IType _2194_elemType = _source95.dtor_elemType;
          unmatched95 = false;
          {
            RAST._IType _2195_eType;
            RAST._IType _out649;
            _out649 = (this).GenType(_2194_elemType, DCOMP.GenTypeContext.@default());
            _2195_eType = _out649;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2195_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
        DAST._IType _2196_elemType = _source95.dtor_elemType;
        DAST._IExpression _2197_collection = _source95.dtor_collection;
        bool _2198_is__forall = _source95.dtor_is__forall;
        DAST._IExpression _2199_lambda = _source95.dtor_lambda;
        unmatched95 = false;
        {
          RAST._IType _2200_tpe;
          RAST._IType _out652;
          _out652 = (this).GenType(_2196_elemType, DCOMP.GenTypeContext.@default());
          _2200_tpe = _out652;
          RAST._IExpr _2201_collectionGen;
          DCOMP._IOwnership _2202___v224;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2203_recIdents;
          RAST._IExpr _out653;
          DCOMP._IOwnership _out654;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
          (this).GenExpr(_2197_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out653, out _out654, out _out655);
          _2201_collectionGen = _out653;
          _2202___v224 = _out654;
          _2203_recIdents = _out655;
          Dafny.ISequence<DAST._IAttribute> _2204_extraAttributes;
          _2204_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2197_collection).is_IntRange) || ((_2197_collection).is_UnboundedIntRange)) || ((_2197_collection).is_SeqBoundedPool)) {
            _2204_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2199_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2205_formals;
            _2205_formals = (_2199_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2206_newFormals;
            _2206_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi49 = new BigInteger((_2205_formals).Count);
            for (BigInteger _2207_i = BigInteger.Zero; _2207_i < _hi49; _2207_i++) {
              var _pat_let_tv141 = _2204_extraAttributes;
              var _pat_let_tv142 = _2205_formals;
              _2206_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2206_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2205_formals).Select(_2207_i), _pat_let38_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let38_0, _2208_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv141, ((_pat_let_tv142).Select(_2207_i)).dtor_attributes), _pat_let39_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let39_0, _2209_dt__update_hattributes_h0 => DAST.Formal.create((_2208_dt__update__tmp_h0).dtor_name, (_2208_dt__update__tmp_h0).dtor_typ, _2209_dt__update_hattributes_h0)))))));
            }
            var _pat_let_tv143 = _2206_newFormals;
            DAST._IExpression _2210_newLambda;
            _2210_newLambda = Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_2199_lambda, _pat_let40_0 => Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_pat_let40_0, _2211_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let_tv143, _pat_let41_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let41_0, _2212_dt__update_hparams_h0 => DAST.Expression.create_Lambda(_2212_dt__update_hparams_h0, (_2211_dt__update__tmp_h1).dtor_retType, (_2211_dt__update__tmp_h1).dtor_body)))));
            RAST._IExpr _2213_lambdaGen;
            DCOMP._IOwnership _2214___v225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2215_recLambdaIdents;
            RAST._IExpr _out656;
            DCOMP._IOwnership _out657;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out658;
            (this).GenExpr(_2210_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out656, out _out657, out _out658);
            _2213_lambdaGen = _out656;
            _2214___v225 = _out657;
            _2215_recLambdaIdents = _out658;
            Dafny.ISequence<Dafny.Rune> _2216_fn;
            _2216_fn = ((_2198_is__forall) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any")));
            r = ((_2201_collectionGen).Sel(_2216_fn)).Apply1(((_2213_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2203_recIdents, _2215_recLambdaIdents);
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
      BigInteger _2217_i;
      _2217_i = BigInteger.Zero;
      while ((_2217_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _2218_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _2219_m;
        RAST._IMod _out661;
        _out661 = (this).GenModule((p).Select(_2217_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2219_m = _out661;
        _2218_generated = (_2219_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_2217_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2218_generated);
        _2217_i = (_2217_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2220_i;
      _2220_i = BigInteger.Zero;
      while ((_2220_i) < (new BigInteger((fullName).Count))) {
        if ((_2220_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2220_i)));
        _2220_i = (_2220_i) + (BigInteger.One);
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