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
      Dafny.ISequence<Dafny.Rune> _1116___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1116___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1116___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1116___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in123 = (i).Drop(new BigInteger(2));
        i = _in123;
        goto TAIL_CALL_START;
      } else {
        _1116___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1116___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in124 = (i).Drop(BigInteger.One);
        i = _in124;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1117___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1117___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1117___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1117___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in125 = (i).Drop(BigInteger.One);
        i = _in125;
        goto TAIL_CALL_START;
      } else {
        _1117___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1117___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _1118_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1118_r);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeField(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1119_r = (f);
      if ((DCOMP.__default.reserved__fields).Contains(_1119_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1119_r);
      } else {
        return DCOMP.__default.escapeName(f);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeDtor(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1120_r = (f);
      if ((DCOMP.__default.reserved__fields).Contains(_1120_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1120_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": r#_")), _1120_r);
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
      var _pat_let_tv136 = dafnyName;
      var _pat_let_tv137 = rs;
      var _pat_let_tv138 = dafnyName;
      if ((new BigInteger((rs).Count)).Sign == 0) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      } else {
        Std.Wrappers._IOption<DAST._IResolvedType> _1121_res = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
          DAST._IType _source51 = (rs).Select(BigInteger.Zero);
          bool unmatched51 = true;
          if (unmatched51) {
            if (_source51.is_UserDefined) {
              DAST._IResolvedType _1122_resolvedType = _source51.dtor_resolved;
              unmatched51 = false;
              return DCOMP.__default.TraitTypeContainingMethod(_1122_resolvedType, _pat_let_tv136);
            }
          }
          if (unmatched51) {
            unmatched51 = false;
            return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
          }
          throw new System.Exception("unexpected control point");
        }))();
        Std.Wrappers._IOption<DAST._IResolvedType> _source52 = _1121_res;
        bool unmatched52 = true;
        if (unmatched52) {
          if (_source52.is_Some) {
            unmatched52 = false;
            return _1121_res;
          }
        }
        if (unmatched52) {
          unmatched52 = false;
          return DCOMP.__default.TraitTypeContainingMethodAux((_pat_let_tv137).Drop(BigInteger.One), _pat_let_tv138);
        }
        throw new System.Exception("unexpected control point");
      }
    }
    public static Std.Wrappers._IOption<DAST._IResolvedType> TraitTypeContainingMethod(DAST._IResolvedType r, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DAST._IResolvedType _let_tmp_rhs53 = r;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1123_path = _let_tmp_rhs53.dtor_path;
      Dafny.ISequence<DAST._IType> _1124_typeArgs = _let_tmp_rhs53.dtor_typeArgs;
      DAST._IResolvedTypeBase _1125_kind = _let_tmp_rhs53.dtor_kind;
      Dafny.ISequence<DAST._IAttribute> _1126_attributes = _let_tmp_rhs53.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1127_properMethods = _let_tmp_rhs53.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1128_extendedTypes = _let_tmp_rhs53.dtor_extendedTypes;
      if ((_1127_properMethods).Contains(dafnyName)) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(r);
      } else {
        return DCOMP.__default.TraitTypeContainingMethodAux(_1128_extendedTypes, dafnyName);
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
      DCOMP._IEnvironment _1129_dt__update__tmp_h0 = this;
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1130_dt__update_htypes_h0 = ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType>>)(() => {
        var _coll6 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in ((this).dtor_types).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _1131_k = (Dafny.ISequence<Dafny.Rune>)_compr_6;
          if (((this).dtor_types).Contains(_1131_k)) {
            _coll6.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>(_1131_k, (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,_1131_k)).ToOwned()));
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IType>.FromCollection(_coll6);
      }))();
      return DCOMP.Environment.create((_1129_dt__update__tmp_h0).dtor_names, _1130_dt__update_htypes_h0);
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
      BigInteger _1132_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1132_indexInEnv), ((this).dtor_names).Drop((_1132_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
      Dafny.ISequence<Dafny.Rune> _1133_modName;
      _1133_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_1133_modName);
      } else {
        Dafny.ISequence<RAST._IModDecl> _1134_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _1134_body = _out15;
        s = RAST.Mod.create_Mod(_1133_modName, _1134_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi5 = new BigInteger((body).Count);
      for (BigInteger _1135_i = BigInteger.Zero; _1135_i < _hi5; _1135_i++) {
        Dafny.ISequence<RAST._IModDecl> _1136_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source53 = (body).Select(_1135_i);
        bool unmatched53 = true;
        if (unmatched53) {
          if (_source53.is_Module) {
            DAST._IModule _1137_m = _source53.dtor_Module_a0;
            unmatched53 = false;
            RAST._IMod _1138_mm;
            RAST._IMod _out16;
            _out16 = (this).GenModule(_1137_m, containingPath);
            _1138_mm = _out16;
            _1136_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1138_mm));
          }
        }
        if (unmatched53) {
          if (_source53.is_Class) {
            DAST._IClass _1139_c = _source53.dtor_Class_a0;
            unmatched53 = false;
            Dafny.ISequence<RAST._IModDecl> _out17;
            _out17 = (this).GenClass(_1139_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1139_c).dtor_name)));
            _1136_generated = _out17;
          }
        }
        if (unmatched53) {
          if (_source53.is_Trait) {
            DAST._ITrait _1140_t = _source53.dtor_Trait_a0;
            unmatched53 = false;
            Dafny.ISequence<RAST._IModDecl> _out18;
            _out18 = (this).GenTrait(_1140_t, containingPath);
            _1136_generated = _out18;
          }
        }
        if (unmatched53) {
          if (_source53.is_Newtype) {
            DAST._INewtype _1141_n = _source53.dtor_Newtype_a0;
            unmatched53 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenNewtype(_1141_n);
            _1136_generated = _out19;
          }
        }
        if (unmatched53) {
          if (_source53.is_SynonymType) {
            DAST._ISynonymType _1142_s = _source53.dtor_SynonymType_a0;
            unmatched53 = false;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenSynonymType(_1142_s);
            _1136_generated = _out20;
          }
        }
        if (unmatched53) {
          DAST._IDatatype _1143_d = _source53.dtor_Datatype_a0;
          unmatched53 = false;
          Dafny.ISequence<RAST._IModDecl> _out21;
          _out21 = (this).GenDatatype(_1143_d);
          _1136_generated = _out21;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1136_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1144_genTpConstraint;
      _1144_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1144_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1144_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1144_genTpConstraint);
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
        for (BigInteger _1145_tpI = BigInteger.Zero; _1145_tpI < _hi6; _1145_tpI++) {
          DAST._ITypeArgDecl _1146_tp;
          _1146_tp = (@params).Select(_1145_tpI);
          DAST._IType _1147_typeArg;
          RAST._ITypeParamDecl _1148_typeParam;
          DAST._IType _out22;
          RAST._ITypeParamDecl _out23;
          (this).GenTypeParam(_1146_tp, out _out22, out _out23);
          _1147_typeArg = _out22;
          _1148_typeParam = _out23;
          RAST._IType _1149_rType;
          RAST._IType _out24;
          _out24 = (this).GenType(_1147_typeArg, DCOMP.GenTypeContext.@default());
          _1149_rType = _out24;
          typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1147_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1149_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1148_typeParam));
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
      Dafny.ISequence<DAST._IType> _1150_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1151_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1152_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1153_whereConstraints;
      Dafny.ISequence<DAST._IType> _out25;
      Dafny.ISequence<RAST._IType> _out26;
      Dafny.ISequence<RAST._ITypeParamDecl> _out27;
      Dafny.ISequence<Dafny.Rune> _out28;
      (this).GenTypeParameters((c).dtor_typeParams, out _out25, out _out26, out _out27, out _out28);
      _1150_typeParamsSeq = _out25;
      _1151_rTypeParams = _out26;
      _1152_rTypeParamsDecls = _out27;
      _1153_whereConstraints = _out28;
      Dafny.ISequence<Dafny.Rune> _1154_constrainedTypeParams;
      _1154_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1152_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1155_fields;
      _1155_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1156_fieldInits;
      _1156_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1157_fieldI = BigInteger.Zero; _1157_fieldI < _hi7; _1157_fieldI++) {
        DAST._IField _1158_field;
        _1158_field = ((c).dtor_fields).Select(_1157_fieldI);
        RAST._IType _1159_fieldType;
        RAST._IType _out29;
        _out29 = (this).GenType(((_1158_field).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
        _1159_fieldType = _out29;
        Dafny.ISequence<Dafny.Rune> _1160_fieldRustName;
        _1160_fieldRustName = DCOMP.__default.escapeName(((_1158_field).dtor_formal).dtor_name);
        _1155_fields = Dafny.Sequence<RAST._IField>.Concat(_1155_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1160_fieldRustName, _1159_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source54 = (_1158_field).dtor_defaultValue;
        bool unmatched54 = true;
        if (unmatched54) {
          if (_source54.is_Some) {
            DAST._IExpression _1161_e = _source54.dtor_value;
            unmatched54 = false;
            {
              RAST._IExpr _1162_expr;
              DCOMP._IOwnership _1163___v48;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1164___v49;
              RAST._IExpr _out30;
              DCOMP._IOwnership _out31;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
              (this).GenExpr(_1161_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
              _1162_expr = _out30;
              _1163___v48 = _out31;
              _1164___v49 = _out32;
              _1156_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1156_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1160_fieldRustName, _1162_expr)));
            }
          }
        }
        if (unmatched54) {
          unmatched54 = false;
          {
            RAST._IExpr _1165_default;
            _1165_default = RAST.__default.std__Default__default;
            if ((_1159_fieldType).IsObjectOrPointer()) {
              _1165_default = (_1159_fieldType).ToNullExpr();
            }
            _1156_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1156_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1160_fieldRustName, _1165_default)));
          }
        }
      }
      BigInteger _hi8 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1166_typeParamI = BigInteger.Zero; _1166_typeParamI < _hi8; _1166_typeParamI++) {
        DAST._IType _1167_typeArg;
        RAST._ITypeParamDecl _1168_typeParam;
        DAST._IType _out33;
        RAST._ITypeParamDecl _out34;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1166_typeParamI), out _out33, out _out34);
        _1167_typeArg = _out33;
        _1168_typeParam = _out34;
        RAST._IType _1169_rTypeArg;
        RAST._IType _out35;
        _out35 = (this).GenType(_1167_typeArg, DCOMP.GenTypeContext.@default());
        _1169_rTypeArg = _out35;
        _1155_fields = Dafny.Sequence<RAST._IField>.Concat(_1155_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1166_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1169_rTypeArg))))));
        _1156_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1156_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1166_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      Dafny.ISequence<Dafny.Rune> _1170_datatypeName;
      _1170_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IStruct _1171_struct;
      _1171_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1170_datatypeName, _1152_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1155_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1171_struct));
      Dafny.ISequence<RAST._IImplMember> _1172_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1173_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out36;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out37;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(path, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Class(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1150_typeParamsSeq, out _out36, out _out37);
      _1172_implBodyRaw = _out36;
      _1173_traitBodies = _out37;
      Dafny.ISequence<RAST._IImplMember> _1174_implBody;
      _1174_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.Type.create_SelfOwned())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel((this).allocate)).ApplyType1(RAST.Type.create_SelfOwned())).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))))), _1172_implBodyRaw);
      RAST._IImpl _1175_i;
      _1175_i = RAST.Impl.create_Impl(_1152_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1170_datatypeName), _1151_rTypeParams), _1153_whereConstraints, _1174_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1175_i)));
      RAST._IType _1176_genSelfPath;
      RAST._IType _out38;
      _out38 = DCOMP.COMP.GenPath(path);
      _1176_genSelfPath = _out38;
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1152_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"))))), RAST.Type.create_TypeApp(_1176_genSelfPath, _1151_rTypeParams), _1153_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any")))))))))));
      BigInteger _hi9 = new BigInteger(((c).dtor_superClasses).Count);
      for (BigInteger _1177_i = BigInteger.Zero; _1177_i < _hi9; _1177_i++) {
        DAST._IType _1178_superClass;
        _1178_superClass = ((c).dtor_superClasses).Select(_1177_i);
        DAST._IType _source55 = _1178_superClass;
        bool unmatched55 = true;
        if (unmatched55) {
          if (_source55.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source55.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1179_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _1180_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
              unmatched55 = false;
              {
                RAST._IType _1181_pathStr;
                RAST._IType _out39;
                _out39 = DCOMP.COMP.GenPath(_1179_traitPath);
                _1181_pathStr = _out39;
                Dafny.ISequence<RAST._IType> _1182_typeArgs;
                Dafny.ISequence<RAST._IType> _out40;
                _out40 = (this).GenTypeArgs(_1180_typeArgs, DCOMP.GenTypeContext.@default());
                _1182_typeArgs = _out40;
                Dafny.ISequence<RAST._IImplMember> _1183_body;
                _1183_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_1173_traitBodies).Contains(_1179_traitPath)) {
                  _1183_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1173_traitBodies,_1179_traitPath);
                }
                RAST._IType _1184_traitType;
                _1184_traitType = RAST.Type.create_TypeApp(_1181_pathStr, _1182_typeArgs);
                RAST._IModDecl _1185_x;
                _1185_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1152_rTypeParamsDecls, _1184_traitType, RAST.Type.create_TypeApp(_1176_genSelfPath, _1151_rTypeParams), _1153_whereConstraints, _1183_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1185_x));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1152_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_1184_traitType))), RAST.Type.create_TypeApp(_1176_genSelfPath, _1151_rTypeParams), _1153_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(_1184_traitType)))))))));
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
      Dafny.ISequence<DAST._IType> _1186_typeParamsSeq;
      _1186_typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1187_typeParamDecls;
      _1187_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1188_typeParams;
      _1188_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _hi10 = new BigInteger(((t).dtor_typeParams).Count);
        for (BigInteger _1189_tpI = BigInteger.Zero; _1189_tpI < _hi10; _1189_tpI++) {
          DAST._ITypeArgDecl _1190_tp;
          _1190_tp = ((t).dtor_typeParams).Select(_1189_tpI);
          DAST._IType _1191_typeArg;
          RAST._ITypeParamDecl _1192_typeParamDecl;
          DAST._IType _out41;
          RAST._ITypeParamDecl _out42;
          (this).GenTypeParam(_1190_tp, out _out41, out _out42);
          _1191_typeArg = _out41;
          _1192_typeParamDecl = _out42;
          _1186_typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(_1186_typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1191_typeArg));
          _1187_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1187_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1192_typeParamDecl));
          RAST._IType _1193_typeParam;
          RAST._IType _out43;
          _out43 = (this).GenType(_1191_typeArg, DCOMP.GenTypeContext.@default());
          _1193_typeParam = _out43;
          _1188_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1188_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1193_typeParam));
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1194_fullPath;
      _1194_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1195_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1196___v54;
      Dafny.ISequence<RAST._IImplMember> _out44;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out45;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1194_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Trait(), (t).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1186_typeParamsSeq, out _out44, out _out45);
      _1195_implBody = _out44;
      _1196___v54 = _out45;
      Dafny.ISequence<RAST._IType> _1197_parents;
      _1197_parents = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi11 = new BigInteger(((t).dtor_parents).Count);
      for (BigInteger _1198_i = BigInteger.Zero; _1198_i < _hi11; _1198_i++) {
        RAST._IType _1199_tpe;
        RAST._IType _out46;
        _out46 = (this).GenType(((t).dtor_parents).Select(_1198_i), DCOMP.GenTypeContext.ForTraitParents());
        _1199_tpe = _out46;
        _1197_parents = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.Concat(_1197_parents, Dafny.Sequence<RAST._IType>.FromElements(_1199_tpe)), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply1(RAST.Type.create_DynType(_1199_tpe))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1187_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1188_typeParams), _1197_parents, _1195_implBody)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1200_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1201_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1202_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1203_whereConstraints;
      Dafny.ISequence<DAST._IType> _out47;
      Dafny.ISequence<RAST._IType> _out48;
      Dafny.ISequence<RAST._ITypeParamDecl> _out49;
      Dafny.ISequence<Dafny.Rune> _out50;
      (this).GenTypeParameters((c).dtor_typeParams, out _out47, out _out48, out _out49, out _out50);
      _1200_typeParamsSeq = _out47;
      _1201_rTypeParams = _out48;
      _1202_rTypeParamsDecls = _out49;
      _1203_whereConstraints = _out50;
      Dafny.ISequence<Dafny.Rune> _1204_constrainedTypeParams;
      _1204_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1202_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1205_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source56 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      bool unmatched56 = true;
      if (unmatched56) {
        if (_source56.is_Some) {
          RAST._IType _1206_v = _source56.dtor_value;
          unmatched56 = false;
          _1205_underlyingType = _1206_v;
        }
      }
      if (unmatched56) {
        unmatched56 = false;
        RAST._IType _out51;
        _out51 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
        _1205_underlyingType = _out51;
      }
      DAST._IType _1207_resultingType;
      _1207_resultingType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _1208_newtypeName;
      _1208_newtypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1208_newtypeName, _1202_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1205_underlyingType))))));
      RAST._IExpr _1209_fnBody;
      _1209_fnBody = RAST.Expr.create_Identifier(_1208_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source57 = (c).dtor_witnessExpr;
      bool unmatched57 = true;
      if (unmatched57) {
        if (_source57.is_Some) {
          DAST._IExpression _1210_e = _source57.dtor_value;
          unmatched57 = false;
          {
            DAST._IExpression _1211_e;
            _1211_e = ((object.Equals((c).dtor_base, _1207_resultingType)) ? (_1210_e) : (DAST.Expression.create_Convert(_1210_e, (c).dtor_base, _1207_resultingType)));
            RAST._IExpr _1212_eStr;
            DCOMP._IOwnership _1213___v55;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1214___v56;
            RAST._IExpr _out52;
            DCOMP._IOwnership _out53;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out54;
            (this).GenExpr(_1211_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out52, out _out53, out _out54);
            _1212_eStr = _out52;
            _1213___v55 = _out53;
            _1214___v56 = _out54;
            _1209_fnBody = (_1209_fnBody).Apply1(_1212_eStr);
          }
        }
      }
      if (unmatched57) {
        unmatched57 = false;
        {
          _1209_fnBody = (_1209_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1215_body;
      _1215_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1209_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source58 = (c).dtor_constraint;
      bool unmatched58 = true;
      if (unmatched58) {
        if (_source58.is_None) {
          unmatched58 = false;
        }
      }
      if (unmatched58) {
        DAST._INewtypeConstraint value8 = _source58.dtor_value;
        DAST._IFormal _1216_formal = value8.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _1217_constraintStmts = value8.dtor_constraintStmts;
        unmatched58 = false;
        RAST._IExpr _1218_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1219___v57;
        DCOMP._IEnvironment _1220_newEnv;
        RAST._IExpr _out55;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out56;
        DCOMP._IEnvironment _out57;
        (this).GenStmts(_1217_constraintStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out55, out _out56, out _out57);
        _1218_rStmts = _out55;
        _1219___v57 = _out56;
        _1220_newEnv = _out57;
        Dafny.ISequence<RAST._IFormal> _1221_rFormals;
        Dafny.ISequence<RAST._IFormal> _out58;
        _out58 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_1216_formal));
        _1221_rFormals = _out58;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1202_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1208_newtypeName), _1201_rTypeParams), _1203_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _1221_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1218_rStmts))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1202_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1208_newtypeName), _1201_rTypeParams), _1203_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1215_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1202_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1208_newtypeName), _1201_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1202_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1208_newtypeName), _1201_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1205_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1222_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1223_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1224_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1225_whereConstraints;
      Dafny.ISequence<DAST._IType> _out59;
      Dafny.ISequence<RAST._IType> _out60;
      Dafny.ISequence<RAST._ITypeParamDecl> _out61;
      Dafny.ISequence<Dafny.Rune> _out62;
      (this).GenTypeParameters((c).dtor_typeParams, out _out59, out _out60, out _out61, out _out62);
      _1222_typeParamsSeq = _out59;
      _1223_rTypeParams = _out60;
      _1224_rTypeParamsDecls = _out61;
      _1225_whereConstraints = _out62;
      Dafny.ISequence<Dafny.Rune> _1226_constrainedTypeParams;
      _1226_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1224_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<Dafny.Rune> _1227_synonymTypeName;
      _1227_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _1228_resultingType;
      RAST._IType _out63;
      _out63 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
      _1228_resultingType = _out63;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1227_synonymTypeName, _1224_rTypeParamsDecls, _1228_resultingType)));
      Std.Wrappers._IOption<DAST._IExpression> _source59 = (c).dtor_witnessExpr;
      bool unmatched59 = true;
      if (unmatched59) {
        if (_source59.is_Some) {
          DAST._IExpression _1229_e = _source59.dtor_value;
          unmatched59 = false;
          {
            RAST._IExpr _1230_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1231___v58;
            DCOMP._IEnvironment _1232_newEnv;
            RAST._IExpr _out64;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out65;
            DCOMP._IEnvironment _out66;
            (this).GenStmts((c).dtor_witnessStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out64, out _out65, out _out66);
            _1230_rStmts = _out64;
            _1231___v58 = _out65;
            _1232_newEnv = _out66;
            RAST._IExpr _1233_rExpr;
            DCOMP._IOwnership _1234___v59;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1235___v60;
            RAST._IExpr _out67;
            DCOMP._IOwnership _out68;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out69;
            (this).GenExpr(_1229_e, DCOMP.SelfInfo.create_NoSelf(), _1232_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out67, out _out68, out _out69);
            _1233_rExpr = _out67;
            _1234___v59 = _out68;
            _1235___v60 = _out69;
            Dafny.ISequence<Dafny.Rune> _1236_constantName;
            _1236_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_1236_constantName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1228_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_1230_rStmts).Then(_1233_rExpr)))))));
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
          Dafny.ISequence<DAST._IType> _1237_ts = _source60.dtor_Tuple_a0;
          unmatched60 = false;
          return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, bool>>((_1238_ts) => Dafny.Helpers.Quantifier<DAST._IType>((_1238_ts).UniqueElements, true, (((_forall_var_5) => {
            DAST._IType _1239_t = (DAST._IType)_forall_var_5;
            return !((_1238_ts).Contains(_1239_t)) || ((this).TypeIsEq(_1239_t));
          }))))(_1237_ts);
        }
      }
      if (unmatched60) {
        if (_source60.is_Array) {
          DAST._IType _1240_t = _source60.dtor_element;
          unmatched60 = false;
          return (this).TypeIsEq(_1240_t);
        }
      }
      if (unmatched60) {
        if (_source60.is_Seq) {
          DAST._IType _1241_t = _source60.dtor_element;
          unmatched60 = false;
          return (this).TypeIsEq(_1241_t);
        }
      }
      if (unmatched60) {
        if (_source60.is_Set) {
          DAST._IType _1242_t = _source60.dtor_element;
          unmatched60 = false;
          return (this).TypeIsEq(_1242_t);
        }
      }
      if (unmatched60) {
        if (_source60.is_Multiset) {
          DAST._IType _1243_t = _source60.dtor_element;
          unmatched60 = false;
          return (this).TypeIsEq(_1243_t);
        }
      }
      if (unmatched60) {
        if (_source60.is_Map) {
          DAST._IType _1244_k = _source60.dtor_key;
          DAST._IType _1245_v = _source60.dtor_value;
          unmatched60 = false;
          return ((this).TypeIsEq(_1244_k)) && ((this).TypeIsEq(_1245_v));
        }
      }
      if (unmatched60) {
        if (_source60.is_SetBuilder) {
          DAST._IType _1246_t = _source60.dtor_element;
          unmatched60 = false;
          return (this).TypeIsEq(_1246_t);
        }
      }
      if (unmatched60) {
        if (_source60.is_MapBuilder) {
          DAST._IType _1247_k = _source60.dtor_key;
          DAST._IType _1248_v = _source60.dtor_value;
          unmatched60 = false;
          return ((this).TypeIsEq(_1247_k)) && ((this).TypeIsEq(_1248_v));
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
          Dafny.ISequence<Dafny.Rune> _1249_i = _source60.dtor_TypeArg_a0;
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
      return (!((c).dtor_isCo)) && (Dafny.Helpers.Id<Func<DAST._IDatatype, bool>>((_1250_c) => Dafny.Helpers.Quantifier<DAST._IDatatypeCtor>(((_1250_c).dtor_ctors).UniqueElements, true, (((_forall_var_6) => {
        DAST._IDatatypeCtor _1251_ctor = (DAST._IDatatypeCtor)_forall_var_6;
        return Dafny.Helpers.Quantifier<DAST._IDatatypeDtor>(((_1251_ctor).dtor_args).UniqueElements, true, (((_forall_var_7) => {
          DAST._IDatatypeDtor _1252_arg = (DAST._IDatatypeDtor)_forall_var_7;
          return !((((_1250_c).dtor_ctors).Contains(_1251_ctor)) && (((_1251_ctor).dtor_args).Contains(_1252_arg))) || ((this).TypeIsEq(((_1252_arg).dtor_formal).dtor_typ));
        })));
      }))))(c));
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1253_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1254_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1255_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1256_whereConstraints;
      Dafny.ISequence<DAST._IType> _out70;
      Dafny.ISequence<RAST._IType> _out71;
      Dafny.ISequence<RAST._ITypeParamDecl> _out72;
      Dafny.ISequence<Dafny.Rune> _out73;
      (this).GenTypeParameters((c).dtor_typeParams, out _out70, out _out71, out _out72, out _out73);
      _1253_typeParamsSeq = _out70;
      _1254_rTypeParams = _out71;
      _1255_rTypeParamsDecls = _out72;
      _1256_whereConstraints = _out73;
      Dafny.ISequence<Dafny.Rune> _1257_datatypeName;
      _1257_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1258_ctors;
      _1258_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      Dafny.ISequence<DAST._IVariance> _1259_variances;
      _1259_variances = Std.Collections.Seq.__default.Map<DAST._ITypeArgDecl, DAST._IVariance>(((System.Func<DAST._ITypeArgDecl, DAST._IVariance>)((_1260_typeParamDecl) => {
        return (_1260_typeParamDecl).dtor_variance;
      })), (c).dtor_typeParams);
      BigInteger _hi12 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1261_i = BigInteger.Zero; _1261_i < _hi12; _1261_i++) {
        DAST._IDatatypeCtor _1262_ctor;
        _1262_ctor = ((c).dtor_ctors).Select(_1261_i);
        Dafny.ISequence<RAST._IField> _1263_ctorArgs;
        _1263_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1264_isNumeric;
        _1264_isNumeric = false;
        BigInteger _hi13 = new BigInteger(((_1262_ctor).dtor_args).Count);
        for (BigInteger _1265_j = BigInteger.Zero; _1265_j < _hi13; _1265_j++) {
          DAST._IDatatypeDtor _1266_dtor;
          _1266_dtor = ((_1262_ctor).dtor_args).Select(_1265_j);
          RAST._IType _1267_formalType;
          RAST._IType _out74;
          _out74 = (this).GenType(((_1266_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
          _1267_formalType = _out74;
          Dafny.ISequence<Dafny.Rune> _1268_formalName;
          _1268_formalName = DCOMP.__default.escapeName(((_1266_dtor).dtor_formal).dtor_name);
          if (((_1265_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1268_formalName))) {
            _1264_isNumeric = true;
          }
          if ((((_1265_j).Sign != 0) && (_1264_isNumeric)) && (!(Std.Strings.__default.OfNat(_1265_j)).Equals(_1268_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1268_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1265_j)));
            _1264_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1263_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1263_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1268_formalName, RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1267_formalType))))));
          } else {
            _1263_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1263_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1268_formalName, _1267_formalType))));
          }
        }
        RAST._IFields _1269_namedFields;
        _1269_namedFields = RAST.Fields.create_NamedFields(_1263_ctorArgs);
        if (_1264_isNumeric) {
          _1269_namedFields = (_1269_namedFields).ToNamelessFields();
        }
        _1258_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1258_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1262_ctor).dtor_name), _1269_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1270_selfPath;
      _1270_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1271_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1272_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out75;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out76;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1270_selfPath, _1253_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype(_1259_variances), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1253_typeParamsSeq, out _out75, out _out76);
      _1271_implBodyRaw = _out75;
      _1272_traitBodies = _out76;
      Dafny.ISequence<RAST._IImplMember> _1273_implBody;
      _1273_implBody = _1271_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1274_emittedFields;
      _1274_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi14 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1275_i = BigInteger.Zero; _1275_i < _hi14; _1275_i++) {
        DAST._IDatatypeCtor _1276_ctor;
        _1276_ctor = ((c).dtor_ctors).Select(_1275_i);
        BigInteger _hi15 = new BigInteger(((_1276_ctor).dtor_args).Count);
        for (BigInteger _1277_j = BigInteger.Zero; _1277_j < _hi15; _1277_j++) {
          DAST._IDatatypeDtor _1278_dtor;
          _1278_dtor = ((_1276_ctor).dtor_args).Select(_1277_j);
          Dafny.ISequence<Dafny.Rune> _1279_callName;
          _1279_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1278_dtor).dtor_callName, DCOMP.__default.escapeName(((_1278_dtor).dtor_formal).dtor_name));
          if (!((_1274_emittedFields).Contains(_1279_callName))) {
            _1274_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1274_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1279_callName));
            RAST._IType _1280_formalType;
            RAST._IType _out77;
            _out77 = (this).GenType(((_1278_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
            _1280_formalType = _out77;
            Dafny.ISequence<RAST._IMatchCase> _1281_cases;
            _1281_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1282_k = BigInteger.Zero; _1282_k < _hi16; _1282_k++) {
              DAST._IDatatypeCtor _1283_ctor2;
              _1283_ctor2 = ((c).dtor_ctors).Select(_1282_k);
              Dafny.ISequence<Dafny.Rune> _1284_pattern;
              _1284_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1257_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1283_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1285_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1286_hasMatchingField;
              _1286_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1287_patternInner;
              _1287_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1288_isNumeric;
              _1288_isNumeric = false;
              BigInteger _hi17 = new BigInteger(((_1283_ctor2).dtor_args).Count);
              for (BigInteger _1289_l = BigInteger.Zero; _1289_l < _hi17; _1289_l++) {
                DAST._IDatatypeDtor _1290_dtor2;
                _1290_dtor2 = ((_1283_ctor2).dtor_args).Select(_1289_l);
                Dafny.ISequence<Dafny.Rune> _1291_patternName;
                _1291_patternName = DCOMP.__default.escapeDtor(((_1290_dtor2).dtor_formal).dtor_name);
                if (((_1289_l).Sign == 0) && ((_1291_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1288_isNumeric = true;
                }
                if (_1288_isNumeric) {
                  _1291_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1290_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1289_l)));
                }
                if (object.Equals(((_1278_dtor).dtor_formal).dtor_name, ((_1290_dtor2).dtor_formal).dtor_name)) {
                  _1286_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1291_patternName);
                }
                _1287_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1287_patternInner, _1291_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1288_isNumeric) {
                _1284_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1284_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1287_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1284_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1284_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1287_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1286_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1285_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1286_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1285_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1286_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1285_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _1292_ctorMatch;
              _1292_ctorMatch = RAST.MatchCase.create(_1284_pattern, RAST.Expr.create_RawExpr(_1285_rhs));
              _1281_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1281_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1292_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1281_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1281_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1257_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _1293_methodBody;
            _1293_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1281_cases);
            _1273_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1273_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1279_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1280_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1293_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _1294_coerceTypes;
      _1294_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1295_rCoerceTypeParams;
      _1295_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _1296_coerceArguments;
      _1296_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _1297_coerceMap;
      _1297_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _1298_rCoerceMap;
      _1298_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1299_coerceMapToArg;
      _1299_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1300_types;
        _1300_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi18 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1301_typeI = BigInteger.Zero; _1301_typeI < _hi18; _1301_typeI++) {
          DAST._ITypeArgDecl _1302_typeParam;
          _1302_typeParam = ((c).dtor_typeParams).Select(_1301_typeI);
          DAST._IType _1303_typeArg;
          RAST._ITypeParamDecl _1304_rTypeParamDecl;
          DAST._IType _out78;
          RAST._ITypeParamDecl _out79;
          (this).GenTypeParam(_1302_typeParam, out _out78, out _out79);
          _1303_typeArg = _out78;
          _1304_rTypeParamDecl = _out79;
          RAST._IType _1305_rTypeArg;
          RAST._IType _out80;
          _out80 = (this).GenType(_1303_typeArg, DCOMP.GenTypeContext.@default());
          _1305_rTypeArg = _out80;
          _1300_types = Dafny.Sequence<RAST._IType>.Concat(_1300_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1305_rTypeArg))));
          if (((_1301_typeI) < (new BigInteger((_1259_variances).Count))) && (((_1259_variances).Select(_1301_typeI)).is_Nonvariant)) {
            _1294_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1294_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1305_rTypeArg));
            goto continue0;
          }
          DAST._ITypeArgDecl _1306_coerceTypeParam;
          _1306_coerceTypeParam = Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_1302_typeParam, _pat_let9_0 => Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_pat_let9_0, _1307_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_1301_typeI)), _pat_let10_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(_pat_let10_0, _1308_dt__update_hname_h0 => DAST.TypeArgDecl.create(_1308_dt__update_hname_h0, (_1307_dt__update__tmp_h0).dtor_bounds, (_1307_dt__update__tmp_h0).dtor_variance)))));
          DAST._IType _1309_coerceTypeArg;
          RAST._ITypeParamDecl _1310_rCoerceTypeParamDecl;
          DAST._IType _out81;
          RAST._ITypeParamDecl _out82;
          (this).GenTypeParam(_1306_coerceTypeParam, out _out81, out _out82);
          _1309_coerceTypeArg = _out81;
          _1310_rCoerceTypeParamDecl = _out82;
          _1297_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_1297_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_1303_typeArg, _1309_coerceTypeArg)));
          RAST._IType _1311_rCoerceType;
          RAST._IType _out83;
          _out83 = (this).GenType(_1309_coerceTypeArg, DCOMP.GenTypeContext.@default());
          _1311_rCoerceType = _out83;
          _1298_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_1298_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_1305_rTypeArg, _1311_rCoerceType)));
          _1294_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1294_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1311_rCoerceType));
          _1295_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1295_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1310_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _1312_coerceFormal;
          _1312_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_1301_typeI));
          _1299_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_1299_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_1305_rTypeArg, _1311_rCoerceType), (RAST.Expr.create_Identifier(_1312_coerceFormal)).Clone())));
          _1296_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_1296_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1312_coerceFormal, RAST.__default.Rc(RAST.Type.create_IntersectionType(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_1305_rTypeArg), _1311_rCoerceType)), RAST.__default.StaticTrait)))));
        continue0: ;
        }
      after0: ;
        _1258_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1258_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1313_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1313_tpe);
})), _1300_types)))));
      }
      bool _1314_cIsEq;
      _1314_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_1314_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _1257_datatypeName, _1255_rTypeParamsDecls, _1258_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1255_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams), _1256_whereConstraints, _1273_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1315_printImplBodyCases;
      _1315_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1316_hashImplBodyCases;
      _1316_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1317_coerceImplBodyCases;
      _1317_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi19 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1318_i = BigInteger.Zero; _1318_i < _hi19; _1318_i++) {
        DAST._IDatatypeCtor _1319_ctor;
        _1319_ctor = ((c).dtor_ctors).Select(_1318_i);
        Dafny.ISequence<Dafny.Rune> _1320_ctorMatch;
        _1320_ctorMatch = DCOMP.__default.escapeName((_1319_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1321_modulePrefix;
        _1321_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1322_ctorName;
        _1322_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1321_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1319_ctor).dtor_name));
        if (((new BigInteger((_1322_ctorName).Count)) >= (new BigInteger(13))) && (((_1322_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1322_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1323_printRhs;
        _1323_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1322_ctorName), (((_1319_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1324_hashRhs;
        _1324_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        Dafny.ISequence<RAST._IAssignIdentifier> _1325_coerceRhsArgs;
        _1325_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _1326_isNumeric;
        _1326_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1327_ctorMatchInner;
        _1327_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi20 = new BigInteger(((_1319_ctor).dtor_args).Count);
        for (BigInteger _1328_j = BigInteger.Zero; _1328_j < _hi20; _1328_j++) {
          DAST._IDatatypeDtor _1329_dtor;
          _1329_dtor = ((_1319_ctor).dtor_args).Select(_1328_j);
          Dafny.ISequence<Dafny.Rune> _1330_patternName;
          _1330_patternName = DCOMP.__default.escapeField(((_1329_dtor).dtor_formal).dtor_name);
          DAST._IType _1331_formalType;
          _1331_formalType = ((_1329_dtor).dtor_formal).dtor_typ;
          if (((_1328_j).Sign == 0) && ((_1330_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1326_isNumeric = true;
          }
          if (_1326_isNumeric) {
            _1330_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1329_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1328_j)));
          }
          _1324_hashRhs = (((_1331_formalType).is_Arrow) ? ((_1324_hashRhs).Then(((RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))))) : ((_1324_hashRhs).Then(((RAST.Expr.create_Identifier(_1330_patternName)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))))));
          _1327_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1327_ctorMatchInner, _1330_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1328_j).Sign == 1) {
            _1323_printRhs = (_1323_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1323_printRhs = (_1323_printRhs).Then(RAST.Expr.create_RawExpr((((_1331_formalType).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \"<function>\")?")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1330_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))))));
          RAST._IExpr _1332_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _1333_formalTpe;
          RAST._IType _out84;
          _out84 = (this).GenType(_1331_formalType, DCOMP.GenTypeContext.@default());
          _1333_formalTpe = _out84;
          DAST._IType _1334_newFormalType;
          _1334_newFormalType = (_1331_formalType).Replace(_1297_coerceMap);
          RAST._IType _1335_newFormalTpe;
          _1335_newFormalTpe = (_1333_formalTpe).Replace(_1298_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1336_upcastConverter;
          _1336_upcastConverter = (this).UpcastConversionLambda(_1331_formalType, _1333_formalTpe, _1334_newFormalType, _1335_newFormalTpe, _1299_coerceMapToArg);
          if ((_1336_upcastConverter).is_Success) {
            RAST._IExpr _1337_coercionFunction;
            _1337_coercionFunction = (_1336_upcastConverter).dtor_value;
            _1332_coerceRhsArg = (_1337_coercionFunction).Apply1(RAST.Expr.create_Identifier(_1330_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_1328_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _1257_datatypeName));
            _1332_coerceRhsArg = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("todo!"))).Apply1(RAST.Expr.create_LiteralString((this.error).dtor_value, false, false));
          }
          _1325_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1325_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1330_patternName, _1332_coerceRhsArg)));
        }
        RAST._IExpr _1338_coerceRhs;
        _1338_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_1257_datatypeName)).MSel(DCOMP.__default.escapeName((_1319_ctor).dtor_name)), _1325_coerceRhsArgs);
        if (_1326_isNumeric) {
          _1320_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1320_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1327_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1320_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1320_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1327_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1319_ctor).dtor_hasAnyArgs) {
          _1323_printRhs = (_1323_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1323_printRhs = (_1323_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1315_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1315_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1257_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1320_ctorMatch), RAST.Expr.create_Block(_1323_printRhs))));
        _1316_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1316_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1257_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1320_ctorMatch), RAST.Expr.create_Block(_1324_hashRhs))));
        _1317_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1317_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1257_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1320_ctorMatch), RAST.Expr.create_Block(_1338_coerceRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IMatchCase> _1339_extraCases;
        _1339_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1257_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}"))));
        _1315_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1315_printImplBodyCases, _1339_extraCases);
        _1316_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1316_hashImplBodyCases, _1339_extraCases);
        _1317_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1317_coerceImplBodyCases, _1339_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1340_defaultConstrainedTypeParams;
      _1340_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1255_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1341_rTypeParamsDeclsWithEq;
      _1341_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1255_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1342_rTypeParamsDeclsWithHash;
      _1342_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1255_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1343_printImplBody;
      _1343_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1315_printImplBodyCases);
      RAST._IExpr _1344_hashImplBody;
      _1344_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1316_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1255_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1255_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1343_printImplBody))))))));
      if ((new BigInteger((_1295_rCoerceTypeParams).Count)).Sign == 1) {
        RAST._IExpr _1345_coerceImplBody;
        _1345_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _1317_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1255_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), _1295_rCoerceTypeParams, _1296_coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams)), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1294_coerceTypes))))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.RcNew(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.Type.create_SelfOwned())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1294_coerceTypes)), _1345_coerceImplBody))))))))));
      }
      if (_1314_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1341_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1342_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1344_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1346_structName;
        _1346_structName = (RAST.Expr.create_Identifier(_1257_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1347_structAssignments;
        _1347_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi21 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1348_i = BigInteger.Zero; _1348_i < _hi21; _1348_i++) {
          DAST._IDatatypeDtor _1349_dtor;
          _1349_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1348_i);
          _1347_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1347_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1349_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1350_defaultConstrainedTypeParams;
        _1350_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1255_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1351_fullType;
        _1351_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams);
        if (_1314_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1350_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1351_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1351_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1346_structName, _1347_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1255_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_1351_fullType), RAST.Type.create_Borrowed(_1351_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
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
        for (BigInteger _1352_i = BigInteger.Zero; _1352_i < _hi22; _1352_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1352_i))));
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
        for (BigInteger _1353_i = BigInteger.Zero; _1353_i < _hi23; _1353_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1353_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, DCOMP._IGenTypeContext genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi24 = new BigInteger((args).Count);
      for (BigInteger _1354_i = BigInteger.Zero; _1354_i < _hi24; _1354_i++) {
        RAST._IType _1355_genTp;
        RAST._IType _out85;
        _out85 = (this).GenType((args).Select(_1354_i), genTypeContext);
        _1355_genTp = _out85;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1355_genTp));
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
          DAST._IResolvedType _1356_resolved = _source61.dtor_resolved;
          unmatched61 = false;
          {
            RAST._IType _1357_t;
            RAST._IType _out86;
            _out86 = DCOMP.COMP.GenPath((_1356_resolved).dtor_path);
            _1357_t = _out86;
            Dafny.ISequence<RAST._IType> _1358_typeArgs;
            Dafny.ISequence<RAST._IType> _out87;
            _out87 = (this).GenTypeArgs((_1356_resolved).dtor_typeArgs, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let11_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let11_0, _1359_dt__update__tmp_h0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let12_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let12_0, _1360_dt__update_hforTraitParents_h0 => DCOMP.GenTypeContext.create((_1359_dt__update__tmp_h0).dtor_inBinding, (_1359_dt__update__tmp_h0).dtor_inFn, _1360_dt__update_hforTraitParents_h0))))));
            _1358_typeArgs = _out87;
            s = RAST.Type.create_TypeApp(_1357_t, _1358_typeArgs);
            DAST._IResolvedTypeBase _source62 = (_1356_resolved).dtor_kind;
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
                  if ((this).IsRcWrapped((_1356_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched62) {
              if (_source62.is_Trait) {
                unmatched62 = false;
                {
                  if (((_1356_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
                  }
                  if (!((genTypeContext).dtor_forTraitParents)) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
              }
            }
            if (unmatched62) {
              DAST._IType _1361_t = _source62.dtor_baseType;
              DAST._INewtypeRange _1362_range = _source62.dtor_range;
              bool _1363_erased = _source62.dtor_erase;
              unmatched62 = false;
              {
                if (_1363_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source63 = DCOMP.COMP.NewtypeToRustType(_1361_t, _1362_range);
                  bool unmatched63 = true;
                  if (unmatched63) {
                    if (_source63.is_Some) {
                      RAST._IType _1364_v = _source63.dtor_value;
                      unmatched63 = false;
                      s = _1364_v;
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
          Dafny.ISequence<DAST._IType> _1365_types = _source61.dtor_Tuple_a0;
          unmatched61 = false;
          {
            Dafny.ISequence<RAST._IType> _1366_args;
            _1366_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1367_i;
            _1367_i = BigInteger.Zero;
            while ((_1367_i) < (new BigInteger((_1365_types).Count))) {
              RAST._IType _1368_generated;
              RAST._IType _out88;
              _out88 = (this).GenType((_1365_types).Select(_1367_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let13_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let13_0, _1369_dt__update__tmp_h1 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let14_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let14_0, _1370_dt__update_hforTraitParents_h1 => DCOMP.GenTypeContext.create((_1369_dt__update__tmp_h1).dtor_inBinding, (_1369_dt__update__tmp_h1).dtor_inFn, _1370_dt__update_hforTraitParents_h1))))));
              _1368_generated = _out88;
              _1366_args = Dafny.Sequence<RAST._IType>.Concat(_1366_args, Dafny.Sequence<RAST._IType>.FromElements(_1368_generated));
              _1367_i = (_1367_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1365_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1366_args)) : (RAST.__default.SystemTupleType(_1366_args)));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Array) {
          DAST._IType _1371_element = _source61.dtor_element;
          BigInteger _1372_dims = _source61.dtor_dims;
          unmatched61 = false;
          {
            if ((_1372_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1373_elem;
              RAST._IType _out89;
              _out89 = (this).GenType(_1371_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let15_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let15_0, _1374_dt__update__tmp_h2 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let16_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let16_0, _1375_dt__update_hforTraitParents_h2 => DCOMP.GenTypeContext.create((_1374_dt__update__tmp_h2).dtor_inBinding, (_1374_dt__update__tmp_h2).dtor_inFn, _1375_dt__update_hforTraitParents_h2))))));
              _1373_elem = _out89;
              if ((_1372_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1373_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1376_n;
                _1376_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1372_dims));
                s = ((RAST.__default.dafny__runtime__type).MSel(_1376_n)).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1373_elem));
                s = (this).Object(s);
              }
            }
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Seq) {
          DAST._IType _1377_element = _source61.dtor_element;
          unmatched61 = false;
          {
            RAST._IType _1378_elem;
            RAST._IType _out90;
            _out90 = (this).GenType(_1377_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let17_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let17_0, _1379_dt__update__tmp_h3 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let18_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let18_0, _1380_dt__update_hforTraitParents_h3 => DCOMP.GenTypeContext.create((_1379_dt__update__tmp_h3).dtor_inBinding, (_1379_dt__update__tmp_h3).dtor_inFn, _1380_dt__update_hforTraitParents_h3))))));
            _1378_elem = _out90;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1378_elem));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Set) {
          DAST._IType _1381_element = _source61.dtor_element;
          unmatched61 = false;
          {
            RAST._IType _1382_elem;
            RAST._IType _out91;
            _out91 = (this).GenType(_1381_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let19_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let19_0, _1383_dt__update__tmp_h4 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let20_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let20_0, _1384_dt__update_hforTraitParents_h4 => DCOMP.GenTypeContext.create((_1383_dt__update__tmp_h4).dtor_inBinding, (_1383_dt__update__tmp_h4).dtor_inFn, _1384_dt__update_hforTraitParents_h4))))));
            _1382_elem = _out91;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1382_elem));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Multiset) {
          DAST._IType _1385_element = _source61.dtor_element;
          unmatched61 = false;
          {
            RAST._IType _1386_elem;
            RAST._IType _out92;
            _out92 = (this).GenType(_1385_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let21_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let21_0, _1387_dt__update__tmp_h5 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let22_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let22_0, _1388_dt__update_hforTraitParents_h5 => DCOMP.GenTypeContext.create((_1387_dt__update__tmp_h5).dtor_inBinding, (_1387_dt__update__tmp_h5).dtor_inFn, _1388_dt__update_hforTraitParents_h5))))));
            _1386_elem = _out92;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1386_elem));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Map) {
          DAST._IType _1389_key = _source61.dtor_key;
          DAST._IType _1390_value = _source61.dtor_value;
          unmatched61 = false;
          {
            RAST._IType _1391_keyType;
            RAST._IType _out93;
            _out93 = (this).GenType(_1389_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let23_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let23_0, _1392_dt__update__tmp_h6 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let24_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let24_0, _1393_dt__update_hforTraitParents_h6 => DCOMP.GenTypeContext.create((_1392_dt__update__tmp_h6).dtor_inBinding, (_1392_dt__update__tmp_h6).dtor_inFn, _1393_dt__update_hforTraitParents_h6))))));
            _1391_keyType = _out93;
            RAST._IType _1394_valueType;
            RAST._IType _out94;
            _out94 = (this).GenType(_1390_value, genTypeContext);
            _1394_valueType = _out94;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1391_keyType, _1394_valueType));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_MapBuilder) {
          DAST._IType _1395_key = _source61.dtor_key;
          DAST._IType _1396_value = _source61.dtor_value;
          unmatched61 = false;
          {
            RAST._IType _1397_keyType;
            RAST._IType _out95;
            _out95 = (this).GenType(_1395_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let25_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let25_0, _1398_dt__update__tmp_h7 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let26_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let26_0, _1399_dt__update_hforTraitParents_h7 => DCOMP.GenTypeContext.create((_1398_dt__update__tmp_h7).dtor_inBinding, (_1398_dt__update__tmp_h7).dtor_inFn, _1399_dt__update_hforTraitParents_h7))))));
            _1397_keyType = _out95;
            RAST._IType _1400_valueType;
            RAST._IType _out96;
            _out96 = (this).GenType(_1396_value, genTypeContext);
            _1400_valueType = _out96;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1397_keyType, _1400_valueType));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_SetBuilder) {
          DAST._IType _1401_elem = _source61.dtor_element;
          unmatched61 = false;
          {
            RAST._IType _1402_elemType;
            RAST._IType _out97;
            _out97 = (this).GenType(_1401_elem, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let27_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let27_0, _1403_dt__update__tmp_h8 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let28_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let28_0, _1404_dt__update_hforTraitParents_h8 => DCOMP.GenTypeContext.create((_1403_dt__update__tmp_h8).dtor_inBinding, (_1403_dt__update__tmp_h8).dtor_inFn, _1404_dt__update_hforTraitParents_h8))))));
            _1402_elemType = _out97;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1402_elemType));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1405_args = _source61.dtor_args;
          DAST._IType _1406_result = _source61.dtor_result;
          unmatched61 = false;
          {
            Dafny.ISequence<RAST._IType> _1407_argTypes;
            _1407_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1408_i;
            _1408_i = BigInteger.Zero;
            while ((_1408_i) < (new BigInteger((_1405_args).Count))) {
              RAST._IType _1409_generated;
              RAST._IType _out98;
              _out98 = (this).GenType((_1405_args).Select(_1408_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let29_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let29_0, _1410_dt__update__tmp_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let30_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let30_0, _1411_dt__update_hforTraitParents_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(true, _pat_let31_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let31_0, _1412_dt__update_hinFn_h0 => DCOMP.GenTypeContext.create((_1410_dt__update__tmp_h9).dtor_inBinding, _1412_dt__update_hinFn_h0, _1411_dt__update_hforTraitParents_h9))))))));
              _1409_generated = _out98;
              _1407_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1407_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1409_generated)));
              _1408_i = (_1408_i) + (BigInteger.One);
            }
            RAST._IType _1413_resultType;
            RAST._IType _out99;
            _out99 = (this).GenType(_1406_result, DCOMP.GenTypeContext.create(((genTypeContext).dtor_inFn) || ((genTypeContext).dtor_inBinding), false, false));
            _1413_resultType = _out99;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1407_argTypes, _1413_resultType)));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source61.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1414_name = _h90;
          unmatched61 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1414_name));
        }
      }
      if (unmatched61) {
        if (_source61.is_Primitive) {
          DAST._IPrimitive _1415_p = _source61.dtor_Primitive_a0;
          unmatched61 = false;
          {
            DAST._IPrimitive _source64 = _1415_p;
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
        Dafny.ISequence<Dafny.Rune> _1416_v = _source61.dtor_Passthrough_a0;
        unmatched61 = false;
        s = RAST.__default.RawType(_1416_v);
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
      for (BigInteger _1417_i = BigInteger.Zero; _1417_i < _hi25; _1417_i++) {
        DAST._IMethod _source65 = (body).Select(_1417_i);
        bool unmatched65 = true;
        if (unmatched65) {
          DAST._IMethod _1418_m = _source65;
          unmatched65 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source66 = (_1418_m).dtor_overridingPath;
            bool unmatched66 = true;
            if (unmatched66) {
              if (_source66.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1419_p = _source66.dtor_value;
                unmatched66 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1420_existing;
                  _1420_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1419_p)) {
                    _1420_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1419_p);
                  }
                  if (((new BigInteger(((_1418_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _1421_genMethod;
                  RAST._IImplMember _out100;
                  _out100 = (this).GenMethod(_1418_m, true, enclosingType, enclosingTypeParams);
                  _1421_genMethod = _out100;
                  _1420_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1420_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1421_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1419_p, _1420_existing)));
                }
              }
            }
            if (unmatched66) {
              unmatched66 = false;
              {
                RAST._IImplMember _1422_generated;
                RAST._IImplMember _out101;
                _out101 = (this).GenMethod(_1418_m, forTrait, enclosingType, enclosingTypeParams);
                _1422_generated = _out101;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1422_generated));
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
      for (BigInteger _1423_i = BigInteger.Zero; _1423_i < _hi26; _1423_i++) {
        DAST._IFormal _1424_param;
        _1424_param = (@params).Select(_1423_i);
        RAST._IType _1425_paramType;
        RAST._IType _out102;
        _out102 = (this).GenType((_1424_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _1425_paramType = _out102;
        if ((!((_1425_paramType).CanReadWithoutClone())) && (!((_1424_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1425_paramType = RAST.Type.create_Borrowed(_1425_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_1424_param).dtor_name), _1425_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1426_params;
      Dafny.ISequence<RAST._IFormal> _out103;
      _out103 = (this).GenParams((m).dtor_params);
      _1426_params = _out103;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1427_paramNames;
      _1427_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1428_paramTypes;
      _1428_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi27 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1429_paramI = BigInteger.Zero; _1429_paramI < _hi27; _1429_paramI++) {
        DAST._IFormal _1430_dafny__formal;
        _1430_dafny__formal = ((m).dtor_params).Select(_1429_paramI);
        RAST._IFormal _1431_formal;
        _1431_formal = (_1426_params).Select(_1429_paramI);
        Dafny.ISequence<Dafny.Rune> _1432_name;
        _1432_name = (_1431_formal).dtor_name;
        _1427_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1427_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1432_name));
        _1428_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1428_paramTypes, _1432_name, (_1431_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1433_fnName;
      _1433_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _1434_selfIdent;
      _1434_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1435_selfId;
        _1435_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((m).dtor_outVarsAreUninitFieldsToAssign) {
          _1435_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv139 = enclosingTypeParams;
        var _pat_let_tv140 = enclosingType;
        DAST._IType _1436_instanceType;
        _1436_instanceType = ((System.Func<DAST._IType>)(() => {
          DAST._IType _source67 = enclosingType;
          bool unmatched67 = true;
          if (unmatched67) {
            if (_source67.is_UserDefined) {
              DAST._IResolvedType _1437_r = _source67.dtor_resolved;
              unmatched67 = false;
              return DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_1437_r, _pat_let32_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let32_0, _1438_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv139, _pat_let33_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let33_0, _1439_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_1438_dt__update__tmp_h0).dtor_path, _1439_dt__update_htypeArgs_h0, (_1438_dt__update__tmp_h0).dtor_kind, (_1438_dt__update__tmp_h0).dtor_attributes, (_1438_dt__update__tmp_h0).dtor_properMethods, (_1438_dt__update__tmp_h0).dtor_extendedTypes))))));
            }
          }
          if (unmatched67) {
            unmatched67 = false;
            return _pat_let_tv140;
          }
          throw new System.Exception("unexpected control point");
        }))();
        if (forTrait) {
          RAST._IFormal _1440_selfFormal;
          _1440_selfFormal = (((m).dtor_wasFunction) ? (RAST.Formal.selfBorrowed) : (RAST.Formal.selfBorrowedMut));
          _1426_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1440_selfFormal), _1426_params);
        } else {
          RAST._IType _1441_tpe;
          RAST._IType _out104;
          _out104 = (this).GenType(_1436_instanceType, DCOMP.GenTypeContext.@default());
          _1441_tpe = _out104;
          if ((_1435_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            _1441_tpe = RAST.Type.create_Borrowed(_1441_tpe);
          } else if ((_1435_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_1441_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _1441_tpe = RAST.__default.SelfBorrowed;
              } else {
                _1441_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              _1441_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.Type.create_SelfOwned()));
            }
          }
          _1426_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1435_selfId, _1441_tpe)), _1426_params);
        }
        _1434_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_1435_selfId, _1436_instanceType);
      }
      Dafny.ISequence<RAST._IType> _1442_retTypeArgs;
      _1442_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1443_typeI;
      _1443_typeI = BigInteger.Zero;
      while ((_1443_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1444_typeExpr;
        RAST._IType _out105;
        _out105 = (this).GenType(((m).dtor_outTypes).Select(_1443_typeI), DCOMP.GenTypeContext.@default());
        _1444_typeExpr = _out105;
        _1442_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1442_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1444_typeExpr));
        _1443_typeI = (_1443_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1445_visibility;
      _1445_visibility = ((forTrait) ? (RAST.Visibility.create_PRIV()) : (RAST.Visibility.create_PUB()));
      Dafny.ISequence<DAST._ITypeArgDecl> _1446_typeParamsFiltered;
      _1446_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi28 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1447_typeParamI = BigInteger.Zero; _1447_typeParamI < _hi28; _1447_typeParamI++) {
        DAST._ITypeArgDecl _1448_typeParam;
        _1448_typeParam = ((m).dtor_typeParams).Select(_1447_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1448_typeParam).dtor_name)))) {
          _1446_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1446_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1448_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1449_typeParams;
      _1449_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1446_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi29 = new BigInteger((_1446_typeParamsFiltered).Count);
        for (BigInteger _1450_i = BigInteger.Zero; _1450_i < _hi29; _1450_i++) {
          DAST._IType _1451_typeArg;
          RAST._ITypeParamDecl _1452_rTypeParamDecl;
          DAST._IType _out106;
          RAST._ITypeParamDecl _out107;
          (this).GenTypeParam((_1446_typeParamsFiltered).Select(_1450_i), out _out106, out _out107);
          _1451_typeArg = _out106;
          _1452_rTypeParamDecl = _out107;
          var _pat_let_tv141 = _1452_rTypeParamDecl;
          _1452_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1452_rTypeParamDecl, _pat_let34_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let34_0, _1453_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Dafny.Sequence<RAST._IType>.Concat((_pat_let_tv141).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default")))), _pat_let35_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let35_0, _1454_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1453_dt__update__tmp_h1).dtor_content, _1454_dt__update_hconstraints_h0)))));
          _1449_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1449_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1452_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1455_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1456_env = DCOMP.Environment.Default();
      RAST._IExpr _1457_preBody;
      _1457_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1458_preAssignNames;
      _1458_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1459_preAssignTypes;
      _1459_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        RAST._IExpr _1460_earlyReturn;
        _1460_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source68 = (m).dtor_outVars;
        bool unmatched68 = true;
        if (unmatched68) {
          if (_source68.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1461_outVars = _source68.dtor_value;
            unmatched68 = false;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1460_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(Dafny.Sequence<RAST._IExpr>.FromElements())));
                BigInteger _hi30 = new BigInteger((_1461_outVars).Count);
                for (BigInteger _1462_outI = BigInteger.Zero; _1462_outI < _hi30; _1462_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1463_outVar;
                  _1463_outVar = (_1461_outVars).Select(_1462_outI);
                  Dafny.ISequence<Dafny.Rune> _1464_outName;
                  _1464_outName = DCOMP.__default.escapeName((_1463_outVar));
                  Dafny.ISequence<Dafny.Rune> _1465_tracker__name;
                  _1465_tracker__name = DCOMP.__default.AddAssignedPrefix(_1464_outName);
                  _1458_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1458_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1465_tracker__name));
                  _1459_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1459_preAssignTypes, _1465_tracker__name, RAST.Type.create_Bool());
                  _1457_preBody = (_1457_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1465_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<RAST._IExpr> _1466_tupleArgs;
                _1466_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
                BigInteger _hi31 = new BigInteger((_1461_outVars).Count);
                for (BigInteger _1467_outI = BigInteger.Zero; _1467_outI < _hi31; _1467_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1468_outVar;
                  _1468_outVar = (_1461_outVars).Select(_1467_outI);
                  RAST._IType _1469_outType;
                  RAST._IType _out108;
                  _out108 = (this).GenType(((m).dtor_outTypes).Select(_1467_outI), DCOMP.GenTypeContext.@default());
                  _1469_outType = _out108;
                  Dafny.ISequence<Dafny.Rune> _1470_outName;
                  _1470_outName = DCOMP.__default.escapeName((_1468_outVar));
                  _1427_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1427_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1470_outName));
                  RAST._IType _1471_outMaybeType;
                  _1471_outMaybeType = (((_1469_outType).CanReadWithoutClone()) ? (_1469_outType) : (RAST.__default.MaybePlaceboType(_1469_outType)));
                  _1428_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1428_paramTypes, _1470_outName, _1471_outMaybeType);
                  RAST._IExpr _1472_outVarReturn;
                  DCOMP._IOwnership _1473___v69;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1474___v70;
                  RAST._IExpr _out109;
                  DCOMP._IOwnership _out110;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out111;
                  (this).GenExpr(DAST.Expression.create_Ident((_1468_outVar)), DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1470_outName), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>, RAST._IType>(_1470_outName, _1471_outMaybeType))), DCOMP.Ownership.create_OwnershipOwned(), out _out109, out _out110, out _out111);
                  _1472_outVarReturn = _out109;
                  _1473___v69 = _out110;
                  _1474___v70 = _out111;
                  _1466_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1466_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1472_outVarReturn));
                }
                if ((new BigInteger((_1466_tupleArgs).Count)) == (BigInteger.One)) {
                  _1460_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1466_tupleArgs).Select(BigInteger.Zero)));
                } else {
                  _1460_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1466_tupleArgs)));
                }
              }
            }
          }
        }
        if (unmatched68) {
          unmatched68 = false;
        }
        _1456_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1458_preAssignNames, _1427_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1459_preAssignTypes, _1428_paramTypes));
        RAST._IExpr _1475_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1476___v71;
        DCOMP._IEnvironment _1477___v72;
        RAST._IExpr _out112;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out113;
        DCOMP._IEnvironment _out114;
        (this).GenStmts((m).dtor_body, _1434_selfIdent, _1456_env, true, _1460_earlyReturn, out _out112, out _out113, out _out114);
        _1475_body = _out112;
        _1476___v71 = _out113;
        _1477___v72 = _out114;
        _1455_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1457_preBody).Then(_1475_body));
      } else {
        _1456_env = DCOMP.Environment.create(_1427_paramNames, _1428_paramTypes);
        _1455_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1445_visibility, RAST.Fn.create(_1433_fnName, _1449_typeParams, _1426_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1442_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1442_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1442_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1455_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1478_declarations;
      _1478_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1479_i;
      _1479_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1480_stmts;
      _1480_stmts = stmts;
      while ((_1479_i) < (new BigInteger((_1480_stmts).Count))) {
        DAST._IStatement _1481_stmt;
        _1481_stmt = (_1480_stmts).Select(_1479_i);
        DAST._IStatement _source69 = _1481_stmt;
        bool unmatched69 = true;
        if (unmatched69) {
          if (_source69.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1482_name = _source69.dtor_name;
            DAST._IType _1483_optType = _source69.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source69.dtor_maybeValue;
            if (maybeValue0.is_None) {
              unmatched69 = false;
              if (((_1479_i) + (BigInteger.One)) < (new BigInteger((_1480_stmts).Count))) {
                DAST._IStatement _source70 = (_1480_stmts).Select((_1479_i) + (BigInteger.One));
                bool unmatched70 = true;
                if (unmatched70) {
                  if (_source70.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source70.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> ident0 = lhs0.dtor_ident;
                      Dafny.ISequence<Dafny.Rune> _1484_name2 = ident0;
                      DAST._IExpression _1485_rhs = _source70.dtor_value;
                      unmatched70 = false;
                      if (object.Equals(_1484_name2, _1482_name)) {
                        _1480_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1480_stmts).Subsequence(BigInteger.Zero, _1479_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1482_name, _1483_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1485_rhs)))), (_1480_stmts).Drop((_1479_i) + (new BigInteger(2))));
                        _1481_stmt = (_1480_stmts).Select(_1479_i);
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
        RAST._IExpr _1486_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1487_recIdents;
        DCOMP._IEnvironment _1488_newEnv2;
        RAST._IExpr _out115;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
        DCOMP._IEnvironment _out117;
        (this).GenStmt(_1481_stmt, selfIdent, newEnv, (isLast) && ((_1479_i) == ((new BigInteger((_1480_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out115, out _out116, out _out117);
        _1486_stmtExpr = _out115;
        _1487_recIdents = _out116;
        _1488_newEnv2 = _out117;
        newEnv = _1488_newEnv2;
        DAST._IStatement _source71 = _1481_stmt;
        bool unmatched71 = true;
        if (unmatched71) {
          if (_source71.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1489_name = _source71.dtor_name;
            unmatched71 = false;
            {
              _1478_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1478_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_1489_name)));
            }
          }
        }
        if (unmatched71) {
          unmatched71 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1487_recIdents, _1478_declarations));
        generated = (generated).Then(_1486_stmtExpr);
        _1479_i = (_1479_i) + (BigInteger.One);
        if ((_1486_stmtExpr).is_Return) {
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
          Dafny.ISequence<Dafny.Rune> _1490_id = ident1;
          unmatched72 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1491_idRust;
            _1491_idRust = DCOMP.__default.escapeName(_1490_id);
            if (((env).IsBorrowed(_1491_idRust)) || ((env).IsBorrowedMut(_1491_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1491_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1491_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1491_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched72) {
        if (_source72.is_Select) {
          DAST._IExpression _1492_on = _source72.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1493_field = _source72.dtor_field;
          unmatched72 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1494_fieldName;
            _1494_fieldName = DCOMP.__default.escapeName(_1493_field);
            RAST._IExpr _1495_onExpr;
            DCOMP._IOwnership _1496_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1497_recIdents;
            RAST._IExpr _out118;
            DCOMP._IOwnership _out119;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out120;
            (this).GenExpr(_1492_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out118, out _out119, out _out120);
            _1495_onExpr = _out118;
            _1496_onOwned = _out119;
            _1497_recIdents = _out120;
            RAST._IExpr _source73 = _1495_onExpr;
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
                Dafny.ISequence<Dafny.Rune> _1498_isAssignedVar;
                _1498_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1494_fieldName);
                if (((newEnv).dtor_names).Contains(_1498_isAssignedVar)) {
                  generated = ((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1494_fieldName), RAST.Expr.create_Identifier(_1498_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1498_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _1498_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _1494_fieldName, rhs);
                }
              }
            }
            if (unmatched73) {
              unmatched73 = false;
              if (!object.Equals(_1495_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _1495_onExpr = ((this).modify__macro).Apply1(_1495_onExpr);
              }
              generated = RAST.__default.AssignMember(_1495_onExpr, _1494_fieldName, rhs);
            }
            readIdents = _1497_recIdents;
            needsIIFE = false;
          }
        }
      }
      if (unmatched72) {
        DAST._IExpression _1499_on = _source72.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1500_indices = _source72.dtor_indices;
        unmatched72 = false;
        {
          RAST._IExpr _1501_onExpr;
          DCOMP._IOwnership _1502_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1503_recIdents;
          RAST._IExpr _out121;
          DCOMP._IOwnership _out122;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out123;
          (this).GenExpr(_1499_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out121, out _out122, out _out123);
          _1501_onExpr = _out121;
          _1502_onOwned = _out122;
          _1503_recIdents = _out123;
          readIdents = _1503_recIdents;
          _1501_onExpr = ((this).modify__macro).Apply1(_1501_onExpr);
          RAST._IExpr _1504_r;
          _1504_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1505_indicesExpr;
          _1505_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi32 = new BigInteger((_1500_indices).Count);
          for (BigInteger _1506_i = BigInteger.Zero; _1506_i < _hi32; _1506_i++) {
            RAST._IExpr _1507_idx;
            DCOMP._IOwnership _1508___v81;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1509_recIdentsIdx;
            RAST._IExpr _out124;
            DCOMP._IOwnership _out125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
            (this).GenExpr((_1500_indices).Select(_1506_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out124, out _out125, out _out126);
            _1507_idx = _out124;
            _1508___v81 = _out125;
            _1509_recIdentsIdx = _out126;
            Dafny.ISequence<Dafny.Rune> _1510_varName;
            _1510_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1506_i));
            _1505_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1505_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1510_varName)));
            _1504_r = (_1504_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1510_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.IntoUsize(_1507_idx))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1509_recIdentsIdx);
          }
          if ((new BigInteger((_1500_indices).Count)) > (BigInteger.One)) {
            _1501_onExpr = (_1501_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1511_rhs;
          _1511_rhs = rhs;
          var _pat_let_tv142 = env;
          if (((_1501_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1501_onExpr).LhsIdentifierName(), _pat_let36_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let36_0, _1512_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv142).GetType(_1512_name), _pat_let37_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let37_0, _1513_tpe => ((_1513_tpe).is_Some) && (((_1513_tpe).dtor_value).IsUninitArray())))))))) {
            _1511_rhs = RAST.__default.MaybeUninitNew(_1511_rhs);
          }
          generated = (_1504_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1501_onExpr, _1505_indicesExpr)), _1511_rhs));
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
          Dafny.ISequence<DAST._IFormal> _1514_fields = _source74.dtor_fields;
          unmatched74 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi33 = new BigInteger((_1514_fields).Count);
            for (BigInteger _1515_i = BigInteger.Zero; _1515_i < _hi33; _1515_i++) {
              DAST._IFormal _1516_field;
              _1516_field = (_1514_fields).Select(_1515_i);
              Dafny.ISequence<Dafny.Rune> _1517_fieldName;
              _1517_fieldName = DCOMP.__default.escapeName((_1516_field).dtor_name);
              RAST._IType _1518_fieldTyp;
              RAST._IType _out127;
              _out127 = (this).GenType((_1516_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _1518_fieldTyp = _out127;
              Dafny.ISequence<Dafny.Rune> _1519_isAssignedVar;
              _1519_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1517_fieldName);
              if (((newEnv).dtor_names).Contains(_1519_isAssignedVar)) {
                RAST._IExpr _1520_rhs;
                DCOMP._IOwnership _1521___v82;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1522___v83;
                RAST._IExpr _out128;
                DCOMP._IOwnership _out129;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out130;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1516_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out128, out _out129, out _out130);
                _1520_rhs = _out128;
                _1521___v82 = _out129;
                _1522___v83 = _out130;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1519_isAssignedVar));
                generated = (generated).Then(((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1517_fieldName), RAST.Expr.create_Identifier(_1519_isAssignedVar), _1520_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1519_isAssignedVar);
              }
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1523_name = _source74.dtor_name;
          DAST._IType _1524_typ = _source74.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source74.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1525_expression = maybeValue1.dtor_value;
            unmatched74 = false;
            {
              RAST._IType _1526_tpe;
              RAST._IType _out131;
              _out131 = (this).GenType(_1524_typ, DCOMP.GenTypeContext.InBinding());
              _1526_tpe = _out131;
              Dafny.ISequence<Dafny.Rune> _1527_varName;
              _1527_varName = DCOMP.__default.escapeName(_1523_name);
              bool _1528_hasCopySemantics;
              _1528_hasCopySemantics = (_1526_tpe).CanReadWithoutClone();
              if (((_1525_expression).is_InitializationValue) && (!(_1528_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1527_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).ApplyType1(_1526_tpe)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1527_varName, RAST.__default.MaybePlaceboType(_1526_tpe));
              } else {
                RAST._IExpr _1529_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1530_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1525_expression).is_InitializationValue) && ((_1526_tpe).IsObjectOrPointer())) {
                  _1529_expr = (_1526_tpe).ToNullExpr();
                  _1530_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1531_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out132;
                  DCOMP._IOwnership _out133;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out134;
                  (this).GenExpr(_1525_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out132, out _out133, out _out134);
                  _1529_expr = _out132;
                  _1531_exprOwnership = _out133;
                  _1530_recIdents = _out134;
                }
                readIdents = _1530_recIdents;
                _1526_tpe = (((_1525_expression).is_NewUninitArray) ? ((_1526_tpe).TypeAtInitialization()) : (_1526_tpe));
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_1523_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1526_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1529_expr));
                newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_1523_name), _1526_tpe);
              }
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1532_name = _source74.dtor_name;
          DAST._IType _1533_typ = _source74.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source74.dtor_maybeValue;
          if (maybeValue2.is_None) {
            unmatched74 = false;
            {
              DAST._IStatement _1534_newStmt;
              _1534_newStmt = DAST.Statement.create_DeclareVar(_1532_name, _1533_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1533_typ)));
              RAST._IExpr _out135;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out136;
              DCOMP._IEnvironment _out137;
              (this).GenStmt(_1534_newStmt, selfIdent, env, isLast, earlyReturn, out _out135, out _out136, out _out137);
              generated = _out135;
              readIdents = _out136;
              newEnv = _out137;
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Assign) {
          DAST._IAssignLhs _1535_lhs = _source74.dtor_lhs;
          DAST._IExpression _1536_expression = _source74.dtor_value;
          unmatched74 = false;
          {
            RAST._IExpr _1537_exprGen;
            DCOMP._IOwnership _1538___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1539_exprIdents;
            RAST._IExpr _out138;
            DCOMP._IOwnership _out139;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out140;
            (this).GenExpr(_1536_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out138, out _out139, out _out140);
            _1537_exprGen = _out138;
            _1538___v84 = _out139;
            _1539_exprIdents = _out140;
            if ((_1535_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1540_rustId;
              _1540_rustId = DCOMP.__default.escapeName(((_1535_lhs).dtor_ident));
              Std.Wrappers._IOption<RAST._IType> _1541_tpe;
              _1541_tpe = (env).GetType(_1540_rustId);
              if (((_1541_tpe).is_Some) && ((((_1541_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1537_exprGen = RAST.__default.MaybePlacebo(_1537_exprGen);
              }
            }
            if (((_1535_lhs).is_Index) && (((_1535_lhs).dtor_expr).is_Ident)) {
              Dafny.ISequence<Dafny.Rune> _1542_rustId;
              _1542_rustId = DCOMP.__default.escapeName(((_1535_lhs).dtor_expr).dtor_name);
              Std.Wrappers._IOption<RAST._IType> _1543_tpe;
              _1543_tpe = (env).GetType(_1542_rustId);
              if (((_1543_tpe).is_Some) && ((((_1543_tpe).dtor_value).ExtractMaybeUninitArrayElement()).is_Some)) {
                _1537_exprGen = RAST.__default.MaybeUninitNew(_1537_exprGen);
              }
            }
            RAST._IExpr _1544_lhsGen;
            bool _1545_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1546_recIdents;
            DCOMP._IEnvironment _1547_resEnv;
            RAST._IExpr _out141;
            bool _out142;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out143;
            DCOMP._IEnvironment _out144;
            (this).GenAssignLhs(_1535_lhs, _1537_exprGen, selfIdent, env, out _out141, out _out142, out _out143, out _out144);
            _1544_lhsGen = _out141;
            _1545_needsIIFE = _out142;
            _1546_recIdents = _out143;
            _1547_resEnv = _out144;
            generated = _1544_lhsGen;
            newEnv = _1547_resEnv;
            if (_1545_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1546_recIdents, _1539_exprIdents);
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_If) {
          DAST._IExpression _1548_cond = _source74.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1549_thnDafny = _source74.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1550_elsDafny = _source74.dtor_els;
          unmatched74 = false;
          {
            RAST._IExpr _1551_cond;
            DCOMP._IOwnership _1552___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1553_recIdents;
            RAST._IExpr _out145;
            DCOMP._IOwnership _out146;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out147;
            (this).GenExpr(_1548_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out145, out _out146, out _out147);
            _1551_cond = _out145;
            _1552___v85 = _out146;
            _1553_recIdents = _out147;
            Dafny.ISequence<Dafny.Rune> _1554_condString;
            _1554_condString = (_1551_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1553_recIdents;
            RAST._IExpr _1555_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1556_thnIdents;
            DCOMP._IEnvironment _1557_thnEnv;
            RAST._IExpr _out148;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out149;
            DCOMP._IEnvironment _out150;
            (this).GenStmts(_1549_thnDafny, selfIdent, env, isLast, earlyReturn, out _out148, out _out149, out _out150);
            _1555_thn = _out148;
            _1556_thnIdents = _out149;
            _1557_thnEnv = _out150;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1556_thnIdents);
            RAST._IExpr _1558_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1559_elsIdents;
            DCOMP._IEnvironment _1560_elsEnv;
            RAST._IExpr _out151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out152;
            DCOMP._IEnvironment _out153;
            (this).GenStmts(_1550_elsDafny, selfIdent, env, isLast, earlyReturn, out _out151, out _out152, out _out153);
            _1558_els = _out151;
            _1559_elsIdents = _out152;
            _1560_elsEnv = _out153;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1559_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1551_cond, _1555_thn, _1558_els);
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1561_lbl = _source74.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1562_body = _source74.dtor_body;
          unmatched74 = false;
          {
            RAST._IExpr _1563_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1564_bodyIdents;
            DCOMP._IEnvironment _1565_env2;
            RAST._IExpr _out154;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out155;
            DCOMP._IEnvironment _out156;
            (this).GenStmts(_1562_body, selfIdent, env, isLast, earlyReturn, out _out154, out _out155, out _out156);
            _1563_body = _out154;
            _1564_bodyIdents = _out155;
            _1565_env2 = _out156;
            readIdents = _1564_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1561_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1563_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_While) {
          DAST._IExpression _1566_cond = _source74.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1567_body = _source74.dtor_body;
          unmatched74 = false;
          {
            RAST._IExpr _1568_cond;
            DCOMP._IOwnership _1569___v86;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1570_recIdents;
            RAST._IExpr _out157;
            DCOMP._IOwnership _out158;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out159;
            (this).GenExpr(_1566_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out157, out _out158, out _out159);
            _1568_cond = _out157;
            _1569___v86 = _out158;
            _1570_recIdents = _out159;
            readIdents = _1570_recIdents;
            RAST._IExpr _1571_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1572_bodyIdents;
            DCOMP._IEnvironment _1573_bodyEnv;
            RAST._IExpr _out160;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out161;
            DCOMP._IEnvironment _out162;
            (this).GenStmts(_1567_body, selfIdent, env, false, earlyReturn, out _out160, out _out161, out _out162);
            _1571_bodyExpr = _out160;
            _1572_bodyIdents = _out161;
            _1573_bodyEnv = _out162;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1572_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1568_cond), _1571_bodyExpr);
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1574_boundName = _source74.dtor_boundName;
          DAST._IType _1575_boundType = _source74.dtor_boundType;
          DAST._IExpression _1576_overExpr = _source74.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1577_body = _source74.dtor_body;
          unmatched74 = false;
          {
            RAST._IExpr _1578_over;
            DCOMP._IOwnership _1579___v87;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1580_recIdents;
            RAST._IExpr _out163;
            DCOMP._IOwnership _out164;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out165;
            (this).GenExpr(_1576_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out163, out _out164, out _out165);
            _1578_over = _out163;
            _1579___v87 = _out164;
            _1580_recIdents = _out165;
            if (((_1576_overExpr).is_MapBoundedPool) || ((_1576_overExpr).is_SetBoundedPool)) {
              _1578_over = ((_1578_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1581_boundTpe;
            RAST._IType _out166;
            _out166 = (this).GenType(_1575_boundType, DCOMP.GenTypeContext.@default());
            _1581_boundTpe = _out166;
            readIdents = _1580_recIdents;
            Dafny.ISequence<Dafny.Rune> _1582_boundRName;
            _1582_boundRName = DCOMP.__default.escapeName(_1574_boundName);
            RAST._IExpr _1583_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1584_bodyIdents;
            DCOMP._IEnvironment _1585_bodyEnv;
            RAST._IExpr _out167;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out168;
            DCOMP._IEnvironment _out169;
            (this).GenStmts(_1577_body, selfIdent, (env).AddAssigned(_1582_boundRName, _1581_boundTpe), false, earlyReturn, out _out167, out _out168, out _out169);
            _1583_bodyExpr = _out167;
            _1584_bodyIdents = _out168;
            _1585_bodyEnv = _out169;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1584_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1582_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1582_boundRName, _1578_over, _1583_bodyExpr);
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1586_toLabel = _source74.dtor_toLabel;
          unmatched74 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source75 = _1586_toLabel;
            bool unmatched75 = true;
            if (unmatched75) {
              if (_source75.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1587_lbl = _source75.dtor_value;
                unmatched75 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1587_lbl)));
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
          Dafny.ISequence<DAST._IStatement> _1588_body = _source74.dtor_body;
          unmatched74 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _1589_selfClone;
              DCOMP._IOwnership _1590___v88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1591___v89;
              RAST._IExpr _out170;
              DCOMP._IOwnership _out171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out172;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out170, out _out171, out _out172);
              _1589_selfClone = _out170;
              _1590___v88 = _out171;
              _1591___v89 = _out172;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1589_selfClone)));
            }
            newEnv = env;
            BigInteger _hi34 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1592_paramI = BigInteger.Zero; _1592_paramI < _hi34; _1592_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1593_param;
              _1593_param = ((env).dtor_names).Select(_1592_paramI);
              RAST._IExpr _1594_paramInit;
              DCOMP._IOwnership _1595___v90;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1596___v91;
              RAST._IExpr _out173;
              DCOMP._IOwnership _out174;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out175;
              (this).GenIdent(_1593_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out173, out _out174, out _out175);
              _1594_paramInit = _out173;
              _1595___v90 = _out174;
              _1596___v91 = _out175;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1593_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1594_paramInit)));
              if (((env).dtor_types).Contains(_1593_param)) {
                RAST._IType _1597_declaredType;
                _1597_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1593_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1593_param, _1597_declaredType);
              }
            }
            RAST._IExpr _1598_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1599_bodyIdents;
            DCOMP._IEnvironment _1600_bodyEnv;
            RAST._IExpr _out176;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
            DCOMP._IEnvironment _out178;
            (this).GenStmts(_1588_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out176, out _out177, out _out178);
            _1598_bodyExpr = _out176;
            _1599_bodyIdents = _out177;
            _1600_bodyEnv = _out178;
            readIdents = _1599_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1598_bodyExpr)));
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
          DAST._IExpression _1601_on = _source74.dtor_on;
          DAST._ICallName _1602_name = _source74.dtor_callName;
          Dafny.ISequence<DAST._IType> _1603_typeArgs = _source74.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1604_args = _source74.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1605_maybeOutVars = _source74.dtor_outs;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1606_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1607_recIdents;
            Dafny.ISequence<RAST._IType> _1608_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _1609_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out180;
            Dafny.ISequence<RAST._IType> _out181;
            Std.Wrappers._IOption<DAST._IResolvedType> _out182;
            (this).GenArgs(selfIdent, _1602_name, _1603_typeArgs, _1604_args, env, out _out179, out _out180, out _out181, out _out182);
            _1606_argExprs = _out179;
            _1607_recIdents = _out180;
            _1608_typeExprs = _out181;
            _1609_fullNameQualifier = _out182;
            readIdents = _1607_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source76 = _1609_fullNameQualifier;
            bool unmatched76 = true;
            if (unmatched76) {
              if (_source76.is_Some) {
                DAST._IResolvedType value9 = _source76.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1610_path = value9.dtor_path;
                Dafny.ISequence<DAST._IType> _1611_onTypeArgs = value9.dtor_typeArgs;
                DAST._IResolvedTypeBase _1612_base = value9.dtor_kind;
                unmatched76 = false;
                RAST._IExpr _1613_fullPath;
                RAST._IExpr _out183;
                _out183 = DCOMP.COMP.GenPathExpr(_1610_path);
                _1613_fullPath = _out183;
                Dafny.ISequence<RAST._IType> _1614_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out184;
                _out184 = (this).GenTypeArgs(_1611_onTypeArgs, DCOMP.GenTypeContext.@default());
                _1614_onTypeExprs = _out184;
                RAST._IExpr _1615_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _1616_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1617_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1612_base).is_Trait) || ((_1612_base).is_Class)) {
                  RAST._IExpr _out185;
                  DCOMP._IOwnership _out186;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out187;
                  (this).GenExpr(_1601_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out185, out _out186, out _out187);
                  _1615_onExpr = _out185;
                  _1616_recOwnership = _out186;
                  _1617_recIdents = _out187;
                  _1615_onExpr = ((this).modify__macro).Apply1(_1615_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1617_recIdents);
                } else {
                  RAST._IExpr _out188;
                  DCOMP._IOwnership _out189;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out190;
                  (this).GenExpr(_1601_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out188, out _out189, out _out190);
                  _1615_onExpr = _out188;
                  _1616_recOwnership = _out189;
                  _1617_recIdents = _out190;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1617_recIdents);
                }
                generated = ((((_1613_fullPath).ApplyType(_1614_onTypeExprs)).MSel(DCOMP.__default.escapeName((_1602_name).dtor_name))).ApplyType(_1608_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_1615_onExpr), _1606_argExprs));
              }
            }
            if (unmatched76) {
              unmatched76 = false;
              RAST._IExpr _1618_onExpr;
              DCOMP._IOwnership _1619___v96;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1620_enclosingIdents;
              RAST._IExpr _out191;
              DCOMP._IOwnership _out192;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out193;
              (this).GenExpr(_1601_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out191, out _out192, out _out193);
              _1618_onExpr = _out191;
              _1619___v96 = _out192;
              _1620_enclosingIdents = _out193;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1620_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _1621_renderedName;
              _1621_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
                DAST._ICallName _source77 = _1602_name;
                bool unmatched77 = true;
                if (unmatched77) {
                  if (_source77.is_CallName) {
                    Dafny.ISequence<Dafny.Rune> _1622_name = _source77.dtor_name;
                    unmatched77 = false;
                    return DCOMP.__default.escapeName(_1622_name);
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
              DAST._IExpression _source78 = _1601_on;
              bool unmatched78 = true;
              if (unmatched78) {
                if (_source78.is_Companion) {
                  unmatched78 = false;
                  {
                    _1618_onExpr = (_1618_onExpr).MSel(_1621_renderedName);
                  }
                }
              }
              if (unmatched78) {
                unmatched78 = false;
                {
                  if (!object.Equals(_1618_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source79 = _1602_name;
                    bool unmatched79 = true;
                    if (unmatched79) {
                      if (_source79.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source79.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _1623_tpe = onType0.dtor_value;
                          unmatched79 = false;
                          RAST._IType _1624_typ;
                          RAST._IType _out194;
                          _out194 = (this).GenType(_1623_tpe, DCOMP.GenTypeContext.@default());
                          _1624_typ = _out194;
                          if (((_1624_typ).IsObjectOrPointer()) && (!object.Equals(_1618_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _1618_onExpr = ((this).modify__macro).Apply1(_1618_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched79) {
                      unmatched79 = false;
                    }
                  }
                  _1618_onExpr = (_1618_onExpr).Sel(_1621_renderedName);
                }
              }
              generated = ((_1618_onExpr).ApplyType(_1608_typeExprs)).Apply(_1606_argExprs);
            }
            if (((_1605_maybeOutVars).is_Some) && ((new BigInteger(((_1605_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1625_outVar;
              _1625_outVar = DCOMP.__default.escapeName((((_1605_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
              if (!((env).CanReadWithoutClone(_1625_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1625_outVar, generated);
            } else if (((_1605_maybeOutVars).is_None) || ((new BigInteger(((_1605_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1626_tmpVar;
              _1626_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1627_tmpId;
              _1627_tmpId = RAST.Expr.create_Identifier(_1626_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1626_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1628_outVars;
              _1628_outVars = (_1605_maybeOutVars).dtor_value;
              BigInteger _hi35 = new BigInteger((_1628_outVars).Count);
              for (BigInteger _1629_outI = BigInteger.Zero; _1629_outI < _hi35; _1629_outI++) {
                Dafny.ISequence<Dafny.Rune> _1630_outVar;
                _1630_outVar = DCOMP.__default.escapeName(((_1628_outVars).Select(_1629_outI)));
                RAST._IExpr _1631_rhs;
                _1631_rhs = (_1627_tmpId).Sel(Std.Strings.__default.OfNat(_1629_outI));
                if (!((env).CanReadWithoutClone(_1630_outVar))) {
                  _1631_rhs = RAST.__default.MaybePlacebo(_1631_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1630_outVar, _1631_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Return) {
          DAST._IExpression _1632_exprDafny = _source74.dtor_expr;
          unmatched74 = false;
          {
            RAST._IExpr _1633_expr;
            DCOMP._IOwnership _1634___v107;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1635_recIdents;
            RAST._IExpr _out195;
            DCOMP._IOwnership _out196;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out197;
            (this).GenExpr(_1632_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out195, out _out196, out _out197);
            _1633_expr = _out195;
            _1634___v107 = _out196;
            _1635_recIdents = _out197;
            readIdents = _1635_recIdents;
            if (isLast) {
              generated = _1633_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1633_expr));
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
        DAST._IExpression _1636_e = _source74.dtor_Print_a0;
        unmatched74 = false;
        {
          RAST._IExpr _1637_printedExpr;
          DCOMP._IOwnership _1638_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1639_recIdents;
          RAST._IExpr _out198;
          DCOMP._IOwnership _out199;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out200;
          (this).GenExpr(_1636_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out198, out _out199, out _out200);
          _1637_printedExpr = _out198;
          _1638_recOwnership = _out199;
          _1639_recIdents = _out200;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1637_printedExpr)));
          readIdents = _1639_recIdents;
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
            bool _1640_b = _h170.dtor_BoolLiteral_a0;
            unmatched81 = false;
            {
              RAST._IExpr _out205;
              DCOMP._IOwnership _out206;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_1640_b), expectedOwnership, out _out205, out _out206);
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
            Dafny.ISequence<Dafny.Rune> _1641_i = _h171.dtor_IntLiteral_a0;
            DAST._IType _1642_t = _h171.dtor_IntLiteral_a1;
            unmatched81 = false;
            {
              DAST._IType _source82 = _1642_t;
              bool unmatched82 = true;
              if (unmatched82) {
                if (_source82.is_Primitive) {
                  DAST._IPrimitive _h70 = _source82.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    unmatched82 = false;
                    {
                      if ((new BigInteger((_1641_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1641_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1641_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched82) {
                DAST._IType _1643_o = _source82;
                unmatched82 = false;
                {
                  RAST._IType _1644_genType;
                  RAST._IType _out207;
                  _out207 = (this).GenType(_1643_o, DCOMP.GenTypeContext.@default());
                  _1644_genType = _out207;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1641_i), _1644_genType);
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
            Dafny.ISequence<Dafny.Rune> _1645_n = _h172.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1646_d = _h172.dtor_DecLiteral_a1;
            DAST._IType _1647_t = _h172.dtor_DecLiteral_a2;
            unmatched81 = false;
            {
              DAST._IType _source83 = _1647_t;
              bool unmatched83 = true;
              if (unmatched83) {
                if (_source83.is_Primitive) {
                  DAST._IPrimitive _h71 = _source83.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    unmatched83 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1645_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1646_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched83) {
                DAST._IType _1648_o = _source83;
                unmatched83 = false;
                {
                  RAST._IType _1649_genType;
                  RAST._IType _out210;
                  _out210 = (this).GenType(_1648_o, DCOMP.GenTypeContext.@default());
                  _1649_genType = _out210;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1645_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1646_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1649_genType);
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
            Dafny.ISequence<Dafny.Rune> _1650_l = _h173.dtor_StringLiteral_a0;
            bool _1651_verbatim = _h173.dtor_verbatim;
            unmatched81 = false;
            {
              if (_1651_verbatim) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Verbatim strings prefixed by @ not supported yet."));
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1650_l, false, _1651_verbatim));
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
            BigInteger _1652_c = _h174.dtor_CharLiteralUTF16_a0;
            unmatched81 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1652_c));
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
            Dafny.Rune _1653_c = _h175.dtor_CharLiteral_a0;
            unmatched81 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1653_c).Value)));
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
        DAST._IType _1654_tpe = _h176.dtor_Null_a0;
        unmatched81 = false;
        {
          RAST._IType _1655_tpeGen;
          RAST._IType _out219;
          _out219 = (this).GenType(_1654_tpe, DCOMP.GenTypeContext.@default());
          _1655_tpeGen = _out219;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null"));
          } else {
            r = RAST.Expr.create_TypeAscription(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _1655_tpeGen);
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
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IBinOp _1656_op = _let_tmp_rhs54.dtor_op;
      DAST._IExpression _1657_lExpr = _let_tmp_rhs54.dtor_left;
      DAST._IExpression _1658_rExpr = _let_tmp_rhs54.dtor_right;
      DAST.Format._IBinaryOpFormat _1659_format = _let_tmp_rhs54.dtor_format2;
      bool _1660_becomesLeftCallsRight;
      _1660_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source84 = _1656_op;
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
      bool _1661_becomesRightCallsLeft;
      _1661_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source85 = _1656_op;
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
      bool _1662_becomesCallLeftRight;
      _1662_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source86 = _1656_op;
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
      DCOMP._IOwnership _1663_expectedLeftOwnership;
      _1663_expectedLeftOwnership = ((_1660_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1661_becomesRightCallsLeft) || (_1662_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1664_expectedRightOwnership;
      _1664_expectedRightOwnership = (((_1660_becomesLeftCallsRight) || (_1662_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1661_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1665_left;
      DCOMP._IOwnership _1666___v112;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1667_recIdentsL;
      RAST._IExpr _out222;
      DCOMP._IOwnership _out223;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out224;
      (this).GenExpr(_1657_lExpr, selfIdent, env, _1663_expectedLeftOwnership, out _out222, out _out223, out _out224);
      _1665_left = _out222;
      _1666___v112 = _out223;
      _1667_recIdentsL = _out224;
      RAST._IExpr _1668_right;
      DCOMP._IOwnership _1669___v113;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1670_recIdentsR;
      RAST._IExpr _out225;
      DCOMP._IOwnership _out226;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out227;
      (this).GenExpr(_1658_rExpr, selfIdent, env, _1664_expectedRightOwnership, out _out225, out _out226, out _out227);
      _1668_right = _out225;
      _1669___v113 = _out226;
      _1670_recIdentsR = _out227;
      DAST._IBinOp _source87 = _1656_op;
      bool unmatched87 = true;
      if (unmatched87) {
        if (_source87.is_In) {
          unmatched87 = false;
          {
            r = ((_1668_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1665_left);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_SeqProperPrefix) {
          unmatched87 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1665_left, _1668_right, _1659_format);
        }
      }
      if (unmatched87) {
        if (_source87.is_SeqPrefix) {
          unmatched87 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1665_left, _1668_right, _1659_format);
        }
      }
      if (unmatched87) {
        if (_source87.is_SetMerge) {
          unmatched87 = false;
          {
            r = ((_1665_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1668_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_SetSubtraction) {
          unmatched87 = false;
          {
            r = ((_1665_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1668_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_SetIntersection) {
          unmatched87 = false;
          {
            r = ((_1665_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1668_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Subset) {
          unmatched87 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1665_left, _1668_right, _1659_format);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_ProperSubset) {
          unmatched87 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1665_left, _1668_right, _1659_format);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_SetDisjoint) {
          unmatched87 = false;
          {
            r = ((_1665_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1668_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MapMerge) {
          unmatched87 = false;
          {
            r = ((_1665_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1668_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MapSubtraction) {
          unmatched87 = false;
          {
            r = ((_1665_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1668_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MultisetMerge) {
          unmatched87 = false;
          {
            r = ((_1665_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1668_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MultisetSubtraction) {
          unmatched87 = false;
          {
            r = ((_1665_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1668_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MultisetIntersection) {
          unmatched87 = false;
          {
            r = ((_1665_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1668_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Submultiset) {
          unmatched87 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1665_left, _1668_right, _1659_format);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_ProperSubmultiset) {
          unmatched87 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1665_left, _1668_right, _1659_format);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MultisetDisjoint) {
          unmatched87 = false;
          {
            r = ((_1665_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1668_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Concat) {
          unmatched87 = false;
          {
            r = ((_1665_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1668_right);
          }
        }
      }
      if (unmatched87) {
        unmatched87 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1656_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1656_op), _1665_left, _1668_right, _1659_format);
          } else {
            DAST._IBinOp _source88 = _1656_op;
            bool unmatched88 = true;
            if (unmatched88) {
              if (_source88.is_Eq) {
                bool _1671_referential = _source88.dtor_referential;
                unmatched88 = false;
                {
                  if (_1671_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1665_left, _1668_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_1658_rExpr).is_SeqValue) && ((new BigInteger(((_1658_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1665_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1657_lExpr).is_SeqValue) && ((new BigInteger(((_1657_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1668_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1665_left, _1668_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
              }
            }
            if (unmatched88) {
              if (_source88.is_EuclidianDiv) {
                unmatched88 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1665_left, _1668_right));
                }
              }
            }
            if (unmatched88) {
              if (_source88.is_EuclidianMod) {
                unmatched88 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1665_left, _1668_right));
                }
              }
            }
            if (unmatched88) {
              Dafny.ISequence<Dafny.Rune> _1672_op = _source88.dtor_Passthrough_a0;
              unmatched88 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1672_op, _1665_left, _1668_right, _1659_format);
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
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1667_recIdentsL, _1670_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _1673_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _1674_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _1675_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _1675_toTpe;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1676_path = _let_tmp_rhs57.dtor_path;
      Dafny.ISequence<DAST._IType> _1677_typeArgs = _let_tmp_rhs57.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs58 = _let_tmp_rhs57.dtor_kind;
      DAST._IType _1678_b = _let_tmp_rhs58.dtor_baseType;
      DAST._INewtypeRange _1679_range = _let_tmp_rhs58.dtor_range;
      bool _1680_erase = _let_tmp_rhs58.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1681___v115 = _let_tmp_rhs57.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1682___v116 = _let_tmp_rhs57.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1683___v117 = _let_tmp_rhs57.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1684_nativeToType;
      _1684_nativeToType = DCOMP.COMP.NewtypeToRustType(_1678_b, _1679_range);
      if (object.Equals(_1674_fromTpe, _1678_b)) {
        RAST._IExpr _1685_recursiveGen;
        DCOMP._IOwnership _1686_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1687_recIdents;
        RAST._IExpr _out230;
        DCOMP._IOwnership _out231;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out232;
        (this).GenExpr(_1673_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out230, out _out231, out _out232);
        _1685_recursiveGen = _out230;
        _1686_recOwned = _out231;
        _1687_recIdents = _out232;
        readIdents = _1687_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source89 = _1684_nativeToType;
        bool unmatched89 = true;
        if (unmatched89) {
          if (_source89.is_Some) {
            RAST._IType _1688_v = _source89.dtor_value;
            unmatched89 = false;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1685_recursiveGen, RAST.Expr.create_ExprFromType(_1688_v)));
            RAST._IExpr _out233;
            DCOMP._IOwnership _out234;
            (this).FromOwned(r, expectedOwnership, out _out233, out _out234);
            r = _out233;
            resultingOwnership = _out234;
          }
        }
        if (unmatched89) {
          unmatched89 = false;
          if (_1680_erase) {
            r = _1685_recursiveGen;
          } else {
            RAST._IType _1689_rhsType;
            RAST._IType _out235;
            _out235 = (this).GenType(_1675_toTpe, DCOMP.GenTypeContext.InBinding());
            _1689_rhsType = _out235;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1689_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1685_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out236;
          DCOMP._IOwnership _out237;
          (this).FromOwnership(r, _1686_recOwned, expectedOwnership, out _out236, out _out237);
          r = _out236;
          resultingOwnership = _out237;
        }
      } else {
        if ((_1684_nativeToType).is_Some) {
          DAST._IType _source90 = _1674_fromTpe;
          bool unmatched90 = true;
          if (unmatched90) {
            if (_source90.is_UserDefined) {
              DAST._IResolvedType resolved1 = _source90.dtor_resolved;
              DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
              if (kind1.is_Newtype) {
                DAST._IType _1690_b0 = kind1.dtor_baseType;
                DAST._INewtypeRange _1691_range0 = kind1.dtor_range;
                bool _1692_erase0 = kind1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1693_attributes0 = resolved1.dtor_attributes;
                unmatched90 = false;
                {
                  Std.Wrappers._IOption<RAST._IType> _1694_nativeFromType;
                  _1694_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1690_b0, _1691_range0);
                  if ((_1694_nativeFromType).is_Some) {
                    RAST._IExpr _1695_recursiveGen;
                    DCOMP._IOwnership _1696_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1697_recIdents;
                    RAST._IExpr _out238;
                    DCOMP._IOwnership _out239;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out240;
                    (this).GenExpr(_1673_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out238, out _out239, out _out240);
                    _1695_recursiveGen = _out238;
                    _1696_recOwned = _out239;
                    _1697_recIdents = _out240;
                    RAST._IExpr _out241;
                    DCOMP._IOwnership _out242;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_1695_recursiveGen, (_1684_nativeToType).dtor_value), _1696_recOwned, expectedOwnership, out _out241, out _out242);
                    r = _out241;
                    resultingOwnership = _out242;
                    readIdents = _1697_recIdents;
                    return ;
                  }
                }
              }
            }
          }
          if (unmatched90) {
            unmatched90 = false;
          }
          if (object.Equals(_1674_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1698_recursiveGen;
            DCOMP._IOwnership _1699_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1700_recIdents;
            RAST._IExpr _out243;
            DCOMP._IOwnership _out244;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out245;
            (this).GenExpr(_1673_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out243, out _out244, out _out245);
            _1698_recursiveGen = _out243;
            _1699_recOwned = _out244;
            _1700_recIdents = _out245;
            RAST._IExpr _out246;
            DCOMP._IOwnership _out247;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_1698_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1684_nativeToType).dtor_value), _1699_recOwned, expectedOwnership, out _out246, out _out247);
            r = _out246;
            resultingOwnership = _out247;
            readIdents = _1700_recIdents;
            return ;
          }
        }
        RAST._IExpr _out248;
        DCOMP._IOwnership _out249;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out250;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1673_expr, _1674_fromTpe, _1678_b), _1678_b, _1675_toTpe), selfIdent, env, expectedOwnership, out _out248, out _out249, out _out250);
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
      DAST._IExpression _let_tmp_rhs59 = e;
      DAST._IExpression _1701_expr = _let_tmp_rhs59.dtor_value;
      DAST._IType _1702_fromTpe = _let_tmp_rhs59.dtor_from;
      DAST._IType _1703_toTpe = _let_tmp_rhs59.dtor_typ;
      DAST._IType _let_tmp_rhs60 = _1702_fromTpe;
      DAST._IResolvedType _let_tmp_rhs61 = _let_tmp_rhs60.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1704___v123 = _let_tmp_rhs61.dtor_path;
      Dafny.ISequence<DAST._IType> _1705___v124 = _let_tmp_rhs61.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs62 = _let_tmp_rhs61.dtor_kind;
      DAST._IType _1706_b = _let_tmp_rhs62.dtor_baseType;
      DAST._INewtypeRange _1707_range = _let_tmp_rhs62.dtor_range;
      bool _1708_erase = _let_tmp_rhs62.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1709_attributes = _let_tmp_rhs61.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1710___v125 = _let_tmp_rhs61.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1711___v126 = _let_tmp_rhs61.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1712_nativeFromType;
      _1712_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1706_b, _1707_range);
      if (object.Equals(_1706_b, _1703_toTpe)) {
        RAST._IExpr _1713_recursiveGen;
        DCOMP._IOwnership _1714_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1715_recIdents;
        RAST._IExpr _out251;
        DCOMP._IOwnership _out252;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out253;
        (this).GenExpr(_1701_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out251, out _out252, out _out253);
        _1713_recursiveGen = _out251;
        _1714_recOwned = _out252;
        _1715_recIdents = _out253;
        readIdents = _1715_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source91 = _1712_nativeFromType;
        bool unmatched91 = true;
        if (unmatched91) {
          if (_source91.is_Some) {
            RAST._IType _1716_v = _source91.dtor_value;
            unmatched91 = false;
            RAST._IType _1717_toTpeRust;
            RAST._IType _out254;
            _out254 = (this).GenType(_1703_toTpe, DCOMP.GenTypeContext.@default());
            _1717_toTpeRust = _out254;
            r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1717_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1713_recursiveGen));
            RAST._IExpr _out255;
            DCOMP._IOwnership _out256;
            (this).FromOwned(r, expectedOwnership, out _out255, out _out256);
            r = _out255;
            resultingOwnership = _out256;
          }
        }
        if (unmatched91) {
          unmatched91 = false;
          if (_1708_erase) {
            r = _1713_recursiveGen;
          } else {
            r = (_1713_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out257;
          DCOMP._IOwnership _out258;
          (this).FromOwnership(r, _1714_recOwned, expectedOwnership, out _out257, out _out258);
          r = _out257;
          resultingOwnership = _out258;
        }
      } else {
        if ((_1712_nativeFromType).is_Some) {
          if (object.Equals(_1703_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1718_recursiveGen;
            DCOMP._IOwnership _1719_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1720_recIdents;
            RAST._IExpr _out259;
            DCOMP._IOwnership _out260;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out261;
            (this).GenExpr(_1701_expr, selfIdent, env, expectedOwnership, out _out259, out _out260, out _out261);
            _1718_recursiveGen = _out259;
            _1719_recOwned = _out260;
            _1720_recIdents = _out261;
            RAST._IExpr _out262;
            DCOMP._IOwnership _out263;
            (this).FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1718_recursiveGen, (this).DafnyCharUnderlying)), _1719_recOwned, expectedOwnership, out _out262, out _out263);
            r = _out262;
            resultingOwnership = _out263;
            readIdents = _1720_recIdents;
            return ;
          }
        }
        RAST._IExpr _out264;
        DCOMP._IOwnership _out265;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out266;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1701_expr, _1702_fromTpe, _1706_b), _1706_b, _1703_toTpe), selfIdent, env, expectedOwnership, out _out264, out _out265, out _out266);
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
        Std.Wrappers._IResult<__T, __E> _1721_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_1721_valueOrError0).IsFailure()) {
          return (_1721_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1722_head = (_1721_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _1723_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_1723_valueOrError1).IsFailure()) {
            return (_1723_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _1724_tail = (_1723_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1722_head), _1724_tail));
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
          RAST._IType _1725_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          RAST._IType _1726_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel((this).upcast)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1725_fromTpeUnderlying, _1726_toTpeUnderlying))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1727_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_1727_valueOrError0).IsFailure()) {
          return (_1727_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1728_lambda = (_1727_valueOrError0).Extract();
          if ((fromType).is_Arrow) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(_1728_lambda);
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).Apply1(_1728_lambda));
          }
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1729_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim12 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr12 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
          for (int i12 = 0; i12 < dim12; i12++) {
            var _1730_i = (BigInteger) i12;
            arr12[(int)(_1730_i)] = (this).UpcastConversionLambda((((fromType).dtor_resolved).dtor_typeArgs).Select(_1730_i), ((fromTpe).dtor_arguments).Select(_1730_i), (((toType).dtor_resolved).dtor_typeArgs).Select(_1730_i), ((toTpe).dtor_arguments).Select(_1730_i), typeParams);
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr12);
        }))());
        if ((_1729_valueOrError1).IsFailure()) {
          return (_1729_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _1731_lambdas = (_1729_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim13 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr13 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim13, "array size exceeds memory limit")];
  for (int i13 = 0; i13 < dim13; i13++) {
    var _1732_i = (BigInteger) i13;
    arr13[(int)(_1732_i)] = ((fromTpe).dtor_arguments).Select(_1732_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr13);
}))())).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_1731_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _1733_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _1734_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _1735_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _1736_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1737_valueOrError2 = (this).UpcastConversionLambda(_1735_newFromType, _1733_newFromTpe, _1736_newToType, _1734_newToTpe, typeParams);
        if ((_1737_valueOrError2).IsFailure()) {
          return (_1737_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1738_coerceArg = (_1737_valueOrError2).Extract();
          RAST._IExpr _1739_collectionType = (RAST.__default.dafny__runtime).MSel(((fromTpe).dtor_baseName).dtor_name);
          RAST._IExpr _1740_baseType = (((((fromTpe).dtor_baseName).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? ((_1739_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((fromTpe).dtor_arguments).Select(BigInteger.Zero), _1733_newFromTpe))) : ((_1739_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1733_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_1740_baseType).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_1738_coerceArg));
        }
      } else if ((((((((((fromTpe).is_DynType) && (((fromTpe).dtor_underlying).is_FnType)) && ((toTpe).is_DynType)) && (((toTpe).dtor_underlying).is_FnType)) && ((((fromTpe).dtor_underlying).dtor_arguments).Equals(((toTpe).dtor_underlying).dtor_arguments))) && ((fromType).is_Arrow)) && ((toType).is_Arrow)) && ((new BigInteger((((fromTpe).dtor_underlying).dtor_arguments).Count)) == (BigInteger.One))) && (((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).is_Borrowed)) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1741_valueOrError3 = (this).UpcastConversionLambda((fromType).dtor_result, ((fromTpe).dtor_underlying).dtor_returnType, (toType).dtor_result, ((toTpe).dtor_underlying).dtor_returnType, typeParams);
        if ((_1741_valueOrError3).IsFailure()) {
          return (_1741_valueOrError3).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1742_lambda = (_1741_valueOrError3).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn1_coerce"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying, ((fromTpe).dtor_underlying).dtor_returnType, ((toTpe).dtor_underlying).dtor_returnType))).Apply1(_1742_lambda));
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
      DAST._IExpression _1743_expr = _let_tmp_rhs63.dtor_value;
      DAST._IType _1744_fromTpe = _let_tmp_rhs63.dtor_from;
      DAST._IType _1745_toTpe = _let_tmp_rhs63.dtor_typ;
      RAST._IType _1746_fromTpeGen;
      RAST._IType _out267;
      _out267 = (this).GenType(_1744_fromTpe, DCOMP.GenTypeContext.InBinding());
      _1746_fromTpeGen = _out267;
      RAST._IType _1747_toTpeGen;
      RAST._IType _out268;
      _out268 = (this).GenType(_1745_toTpe, DCOMP.GenTypeContext.InBinding());
      _1747_toTpeGen = _out268;
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1748_upcastConverter;
      _1748_upcastConverter = (this).UpcastConversionLambda(_1744_fromTpe, _1746_fromTpeGen, _1745_toTpe, _1747_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_1748_upcastConverter).is_Success) {
        RAST._IExpr _1749_conversionLambda;
        _1749_conversionLambda = (_1748_upcastConverter).dtor_value;
        RAST._IExpr _1750_recursiveGen;
        DCOMP._IOwnership _1751_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1752_recIdents;
        RAST._IExpr _out269;
        DCOMP._IOwnership _out270;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out271;
        (this).GenExpr(_1743_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out269, out _out270, out _out271);
        _1750_recursiveGen = _out269;
        _1751_recOwned = _out270;
        _1752_recIdents = _out271;
        readIdents = _1752_recIdents;
        r = (_1749_conversionLambda).Apply1(_1750_recursiveGen);
        RAST._IExpr _out272;
        DCOMP._IOwnership _out273;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out272, out _out273);
        r = _out272;
        resultingOwnership = _out273;
      } else if ((this).IsDowncastConversion(_1746_fromTpeGen, _1747_toTpeGen)) {
        RAST._IExpr _1753_recursiveGen;
        DCOMP._IOwnership _1754_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1755_recIdents;
        RAST._IExpr _out274;
        DCOMP._IOwnership _out275;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out276;
        (this).GenExpr(_1743_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out274, out _out275, out _out276);
        _1753_recursiveGen = _out274;
        _1754_recOwned = _out275;
        _1755_recIdents = _out276;
        readIdents = _1755_recIdents;
        _1747_toTpeGen = (_1747_toTpeGen).ObjectOrPointerUnderlying();
        r = ((RAST.__default.dafny__runtime).MSel((this).downcast)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1753_recursiveGen, RAST.Expr.create_ExprFromType(_1747_toTpeGen)));
        RAST._IExpr _out277;
        DCOMP._IOwnership _out278;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out277, out _out278);
        r = _out277;
        resultingOwnership = _out278;
      } else {
        RAST._IExpr _1756_recursiveGen;
        DCOMP._IOwnership _1757_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1758_recIdents;
        RAST._IExpr _out279;
        DCOMP._IOwnership _out280;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out281;
        (this).GenExpr(_1743_expr, selfIdent, env, expectedOwnership, out _out279, out _out280, out _out281);
        _1756_recursiveGen = _out279;
        _1757_recOwned = _out280;
        _1758_recIdents = _out281;
        readIdents = _1758_recIdents;
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _let_tmp_rhs64 = _1748_upcastConverter;
        _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>> _let_tmp_rhs65 = _let_tmp_rhs64.dtor_error;
        DAST._IType _1759_fromType = _let_tmp_rhs65.dtor__0;
        RAST._IType _1760_fromTpeGen = _let_tmp_rhs65.dtor__1;
        DAST._IType _1761_toType = _let_tmp_rhs65.dtor__2;
        RAST._IType _1762_toTpeGen = _let_tmp_rhs65.dtor__3;
        Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1763_m = _let_tmp_rhs65.dtor__4;
        Dafny.ISequence<Dafny.Rune> _1764_msg;
        _1764_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1760_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1762_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1764_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1756_recursiveGen)._ToString(DCOMP.__default.IND), _1764_msg));
        RAST._IExpr _out282;
        DCOMP._IOwnership _out283;
        (this).FromOwnership(r, _1757_recOwned, expectedOwnership, out _out282, out _out283);
        r = _out282;
        resultingOwnership = _out283;
      }
    }
    public void GenExprConvert(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs66 = e;
      DAST._IExpression _1765_expr = _let_tmp_rhs66.dtor_value;
      DAST._IType _1766_fromTpe = _let_tmp_rhs66.dtor_from;
      DAST._IType _1767_toTpe = _let_tmp_rhs66.dtor_typ;
      if (object.Equals(_1766_fromTpe, _1767_toTpe)) {
        RAST._IExpr _1768_recursiveGen;
        DCOMP._IOwnership _1769_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1770_recIdents;
        RAST._IExpr _out284;
        DCOMP._IOwnership _out285;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out286;
        (this).GenExpr(_1765_expr, selfIdent, env, expectedOwnership, out _out284, out _out285, out _out286);
        _1768_recursiveGen = _out284;
        _1769_recOwned = _out285;
        _1770_recIdents = _out286;
        r = _1768_recursiveGen;
        RAST._IExpr _out287;
        DCOMP._IOwnership _out288;
        (this).FromOwnership(r, _1769_recOwned, expectedOwnership, out _out287, out _out288);
        r = _out287;
        resultingOwnership = _out288;
        readIdents = _1770_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source92 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1766_fromTpe, _1767_toTpe);
        bool unmatched92 = true;
        if (unmatched92) {
          DAST._IType _10 = _source92.dtor__1;
          if (_10.is_UserDefined) {
            DAST._IResolvedType resolved2 = _10.dtor_resolved;
            DAST._IResolvedTypeBase kind2 = resolved2.dtor_kind;
            if (kind2.is_Newtype) {
              DAST._IType _1771_b = kind2.dtor_baseType;
              DAST._INewtypeRange _1772_range = kind2.dtor_range;
              bool _1773_erase = kind2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1774_attributes = resolved2.dtor_attributes;
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
              DAST._IType _1775_b = kind3.dtor_baseType;
              DAST._INewtypeRange _1776_range = kind3.dtor_range;
              bool _1777_erase = kind3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1778_attributes = resolved3.dtor_attributes;
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
                    RAST._IExpr _1779_recursiveGen;
                    DCOMP._IOwnership _1780___v137;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1781_recIdents;
                    RAST._IExpr _out295;
                    DCOMP._IOwnership _out296;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out297;
                    (this).GenExpr(_1765_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out295, out _out296, out _out297);
                    _1779_recursiveGen = _out295;
                    _1780___v137 = _out296;
                    _1781_recIdents = _out297;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1779_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out298;
                    DCOMP._IOwnership _out299;
                    (this).FromOwned(r, expectedOwnership, out _out298, out _out299);
                    r = _out298;
                    resultingOwnership = _out299;
                    readIdents = _1781_recIdents;
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
                    RAST._IExpr _1782_recursiveGen;
                    DCOMP._IOwnership _1783___v138;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1784_recIdents;
                    RAST._IExpr _out300;
                    DCOMP._IOwnership _out301;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out302;
                    (this).GenExpr(_1765_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out300, out _out301, out _out302);
                    _1782_recursiveGen = _out300;
                    _1783___v138 = _out301;
                    _1784_recIdents = _out302;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1782_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out303;
                    DCOMP._IOwnership _out304;
                    (this).FromOwned(r, expectedOwnership, out _out303, out _out304);
                    r = _out303;
                    resultingOwnership = _out304;
                    readIdents = _1784_recIdents;
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
                  RAST._IType _1785_rhsType;
                  RAST._IType _out305;
                  _out305 = (this).GenType(_1767_toTpe, DCOMP.GenTypeContext.InBinding());
                  _1785_rhsType = _out305;
                  RAST._IExpr _1786_recursiveGen;
                  DCOMP._IOwnership _1787___v140;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1788_recIdents;
                  RAST._IExpr _out306;
                  DCOMP._IOwnership _out307;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out308;
                  (this).GenExpr(_1765_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out306, out _out307, out _out308);
                  _1786_recursiveGen = _out306;
                  _1787___v140 = _out307;
                  _1788_recIdents = _out308;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1785_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1786_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out309;
                  DCOMP._IOwnership _out310;
                  (this).FromOwned(r, expectedOwnership, out _out309, out _out310);
                  r = _out309;
                  resultingOwnership = _out310;
                  readIdents = _1788_recIdents;
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
                  RAST._IType _1789_rhsType;
                  RAST._IType _out311;
                  _out311 = (this).GenType(_1766_fromTpe, DCOMP.GenTypeContext.InBinding());
                  _1789_rhsType = _out311;
                  RAST._IExpr _1790_recursiveGen;
                  DCOMP._IOwnership _1791___v142;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1792_recIdents;
                  RAST._IExpr _out312;
                  DCOMP._IOwnership _out313;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out314;
                  (this).GenExpr(_1765_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out312, out _out313, out _out314);
                  _1790_recursiveGen = _out312;
                  _1791___v142 = _out313;
                  _1792_recIdents = _out314;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_1790_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out315;
                  DCOMP._IOwnership _out316;
                  (this).FromOwned(r, expectedOwnership, out _out315, out _out316);
                  r = _out315;
                  resultingOwnership = _out316;
                  readIdents = _1792_recIdents;
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
                    RAST._IType _1793_rhsType;
                    RAST._IType _out317;
                    _out317 = (this).GenType(_1767_toTpe, DCOMP.GenTypeContext.InBinding());
                    _1793_rhsType = _out317;
                    RAST._IExpr _1794_recursiveGen;
                    DCOMP._IOwnership _1795___v143;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1796_recIdents;
                    RAST._IExpr _out318;
                    DCOMP._IOwnership _out319;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out320;
                    (this).GenExpr(_1765_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out318, out _out319, out _out320);
                    _1794_recursiveGen = _out318;
                    _1795___v143 = _out319;
                    _1796_recIdents = _out320;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1794_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out321;
                    DCOMP._IOwnership _out322;
                    (this).FromOwned(r, expectedOwnership, out _out321, out _out322);
                    r = _out321;
                    resultingOwnership = _out322;
                    readIdents = _1796_recIdents;
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
                    RAST._IType _1797_rhsType;
                    RAST._IType _out323;
                    _out323 = (this).GenType(_1766_fromTpe, DCOMP.GenTypeContext.InBinding());
                    _1797_rhsType = _out323;
                    RAST._IExpr _1798_recursiveGen;
                    DCOMP._IOwnership _1799___v144;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1800_recIdents;
                    RAST._IExpr _out324;
                    DCOMP._IOwnership _out325;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out326;
                    (this).GenExpr(_1765_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out324, out _out325, out _out326);
                    _1798_recursiveGen = _out324;
                    _1799___v144 = _out325;
                    _1800_recIdents = _out326;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1798_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out327;
                    DCOMP._IOwnership _out328;
                    (this).FromOwned(r, expectedOwnership, out _out327, out _out328);
                    r = _out327;
                    resultingOwnership = _out328;
                    readIdents = _1800_recIdents;
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
                RAST._IExpr _1801_recursiveGen;
                DCOMP._IOwnership _1802___v147;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1803_recIdents;
                RAST._IExpr _out329;
                DCOMP._IOwnership _out330;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
                (this).GenExpr(_1765_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out329, out _out330, out _out331);
                _1801_recursiveGen = _out329;
                _1802___v147 = _out330;
                _1803_recIdents = _out331;
                RAST._IType _1804_toTpeGen;
                RAST._IType _out332;
                _out332 = (this).GenType(_1767_toTpe, DCOMP.GenTypeContext.InBinding());
                _1804_toTpeGen = _out332;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1801_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1804_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out333;
                DCOMP._IOwnership _out334;
                (this).FromOwned(r, expectedOwnership, out _out333, out _out334);
                r = _out333;
                resultingOwnership = _out334;
                readIdents = _1803_recIdents;
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
      Std.Wrappers._IOption<RAST._IType> _1805_tpe;
      _1805_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1806_placeboOpt;
      _1806_placeboOpt = (((_1805_tpe).is_Some) ? (((_1805_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _1807_currentlyBorrowed;
      _1807_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1808_noNeedOfClone;
      _1808_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1806_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _1807_currentlyBorrowed = false;
        _1808_noNeedOfClone = true;
        _1805_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_1806_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = ((_1807_currentlyBorrowed) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()));
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_1805_tpe).is_Some) && (((_1805_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _1809_needObjectFromRef;
        _1809_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source93 = (selfIdent).dtor_dafnyType;
          bool unmatched93 = true;
          if (unmatched93) {
            if (_source93.is_UserDefined) {
              DAST._IResolvedType resolved4 = _source93.dtor_resolved;
              DAST._IResolvedTypeBase _1810_base = resolved4.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _1811_attributes = resolved4.dtor_attributes;
              unmatched93 = false;
              return ((_1810_base).is_Class) || ((_1810_base).is_Trait);
            }
          }
          if (unmatched93) {
            unmatched93 = false;
            return false;
          }
          throw new System.Exception("unexpected control point");
        }))());
        if (_1809_needObjectFromRef) {
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_1808_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1808_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1807_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_1805_tpe).is_Some) && (((_1805_tpe).dtor_value).IsPointer())) {
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
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_1812_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_1812_attributes).UniqueElements, false, (((_exists_var_1) => {
        DAST._IAttribute _1813_attribute = (DAST._IAttribute)_exists_var_1;
        return ((_1812_attributes).Contains(_1813_attribute)) && ((((_1813_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_1813_attribute).dtor_args).Count)) == (new BigInteger(2))));
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
      for (BigInteger _1814_i = BigInteger.Zero; _1814_i < _hi36; _1814_i++) {
        DCOMP._IOwnership _1815_argOwnership;
        _1815_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if (((name).is_CallName) && ((_1814_i) < (new BigInteger((((name).dtor_signature)).Count)))) {
          RAST._IType _1816_tpe;
          RAST._IType _out338;
          _out338 = (this).GenType(((((name).dtor_signature)).Select(_1814_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _1816_tpe = _out338;
          if ((_1816_tpe).CanReadWithoutClone()) {
            _1815_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _1817_argExpr;
        DCOMP._IOwnership _1818___v154;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1819_argIdents;
        RAST._IExpr _out339;
        DCOMP._IOwnership _out340;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out341;
        (this).GenExpr((args).Select(_1814_i), selfIdent, env, _1815_argOwnership, out _out339, out _out340, out _out341);
        _1817_argExpr = _out339;
        _1818___v154 = _out340;
        _1819_argIdents = _out341;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1817_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1819_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi37 = new BigInteger((typeArgs).Count);
      for (BigInteger _1820_typeI = BigInteger.Zero; _1820_typeI < _hi37; _1820_typeI++) {
        RAST._IType _1821_typeExpr;
        RAST._IType _out342;
        _out342 = (this).GenType((typeArgs).Select(_1820_typeI), DCOMP.GenTypeContext.@default());
        _1821_typeExpr = _out342;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1821_typeExpr));
      }
      fullNameQualifier = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
        DAST._ICallName _source94 = name;
        bool unmatched94 = true;
        if (unmatched94) {
          if (_source94.is_CallName) {
            Dafny.ISequence<Dafny.Rune> _1822_nameIdent = _source94.dtor_name;
            Std.Wrappers._IOption<DAST._IType> onType1 = _source94.dtor_onType;
            if (onType1.is_Some) {
              DAST._IType value10 = onType1.dtor_value;
              if (value10.is_UserDefined) {
                DAST._IResolvedType _1823_resolvedType = value10.dtor_resolved;
                unmatched94 = false;
                if ((((_1823_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_1824_resolvedType, _1825_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(((_1824_resolvedType).dtor_properMethods).UniqueElements, true, (((_forall_var_8) => {
                  Dafny.ISequence<Dafny.Rune> _1826_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_8;
                  return !(((_1824_resolvedType).dtor_properMethods).Contains(_1826_m)) || (!object.Equals((_1826_m), _1825_nameIdent));
                }))))(_1823_resolvedType, _1822_nameIdent))) {
                  return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_1823_resolvedType, (_1822_nameIdent)), _1823_resolvedType));
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
          Dafny.ISequence<Dafny.Rune> _1827_name = _source95.dtor_name;
          unmatched95 = false;
          {
            RAST._IExpr _out346;
            DCOMP._IOwnership _out347;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out348;
            (this).GenIdent(DCOMP.__default.escapeName(_1827_name), selfIdent, env, expectedOwnership, out _out346, out _out347, out _out348);
            r = _out346;
            resultingOwnership = _out347;
            readIdents = _out348;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1828_path = _source95.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _1829_typeArgs = _source95.dtor_typeArgs;
          unmatched95 = false;
          {
            RAST._IExpr _out349;
            _out349 = DCOMP.COMP.GenPathExpr(_1828_path);
            r = _out349;
            if ((new BigInteger((_1829_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1830_typeExprs;
              _1830_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi38 = new BigInteger((_1829_typeArgs).Count);
              for (BigInteger _1831_i = BigInteger.Zero; _1831_i < _hi38; _1831_i++) {
                RAST._IType _1832_typeExpr;
                RAST._IType _out350;
                _out350 = (this).GenType((_1829_typeArgs).Select(_1831_i), DCOMP.GenTypeContext.@default());
                _1832_typeExpr = _out350;
                _1830_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1830_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1832_typeExpr));
              }
              r = (r).ApplyType(_1830_typeExprs);
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
          DAST._IType _1833_typ = _source95.dtor_typ;
          unmatched95 = false;
          {
            RAST._IType _1834_typExpr;
            RAST._IType _out353;
            _out353 = (this).GenType(_1833_typ, DCOMP.GenTypeContext.@default());
            _1834_typExpr = _out353;
            if ((_1834_typExpr).IsObjectOrPointer()) {
              r = (_1834_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1834_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
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
          Dafny.ISequence<DAST._IExpression> _1835_values = _source95.dtor_Tuple_a0;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1836_exprs;
            _1836_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi39 = new BigInteger((_1835_values).Count);
            for (BigInteger _1837_i = BigInteger.Zero; _1837_i < _hi39; _1837_i++) {
              RAST._IExpr _1838_recursiveGen;
              DCOMP._IOwnership _1839___v159;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1840_recIdents;
              RAST._IExpr _out356;
              DCOMP._IOwnership _out357;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out358;
              (this).GenExpr((_1835_values).Select(_1837_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out356, out _out357, out _out358);
              _1838_recursiveGen = _out356;
              _1839___v159 = _out357;
              _1840_recIdents = _out358;
              _1836_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1836_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1838_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1840_recIdents);
            }
            r = (((new BigInteger((_1835_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_1836_exprs)) : (RAST.__default.SystemTuple(_1836_exprs)));
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
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1841_path = _source95.dtor_path;
          Dafny.ISequence<DAST._IType> _1842_typeArgs = _source95.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1843_args = _source95.dtor_args;
          unmatched95 = false;
          {
            RAST._IExpr _out361;
            _out361 = DCOMP.COMP.GenPathExpr(_1841_path);
            r = _out361;
            if ((new BigInteger((_1842_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1844_typeExprs;
              _1844_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi40 = new BigInteger((_1842_typeArgs).Count);
              for (BigInteger _1845_i = BigInteger.Zero; _1845_i < _hi40; _1845_i++) {
                RAST._IType _1846_typeExpr;
                RAST._IType _out362;
                _out362 = (this).GenType((_1842_typeArgs).Select(_1845_i), DCOMP.GenTypeContext.@default());
                _1846_typeExpr = _out362;
                _1844_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1844_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1846_typeExpr));
              }
              r = (r).ApplyType(_1844_typeExprs);
            }
            r = (r).MSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1847_arguments;
            _1847_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi41 = new BigInteger((_1843_args).Count);
            for (BigInteger _1848_i = BigInteger.Zero; _1848_i < _hi41; _1848_i++) {
              RAST._IExpr _1849_recursiveGen;
              DCOMP._IOwnership _1850___v160;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1851_recIdents;
              RAST._IExpr _out363;
              DCOMP._IOwnership _out364;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out365;
              (this).GenExpr((_1843_args).Select(_1848_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out363, out _out364, out _out365);
              _1849_recursiveGen = _out363;
              _1850___v160 = _out364;
              _1851_recIdents = _out365;
              _1847_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1847_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1849_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1851_recIdents);
            }
            r = (r).Apply(_1847_arguments);
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
          Dafny.ISequence<DAST._IExpression> _1852_dims = _source95.dtor_dims;
          DAST._IType _1853_typ = _source95.dtor_typ;
          unmatched95 = false;
          {
            if ((new BigInteger(16)) < (new BigInteger((_1852_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _1854_msg;
              _1854_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1854_msg);
              }
              r = RAST.Expr.create_RawExpr(_1854_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _1855_typeGen;
              RAST._IType _out368;
              _out368 = (this).GenType(_1853_typ, DCOMP.GenTypeContext.@default());
              _1855_typeGen = _out368;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _1856_dimExprs;
              _1856_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi42 = new BigInteger((_1852_dims).Count);
              for (BigInteger _1857_i = BigInteger.Zero; _1857_i < _hi42; _1857_i++) {
                RAST._IExpr _1858_recursiveGen;
                DCOMP._IOwnership _1859___v161;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1860_recIdents;
                RAST._IExpr _out369;
                DCOMP._IOwnership _out370;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out371;
                (this).GenExpr((_1852_dims).Select(_1857_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out369, out _out370, out _out371);
                _1858_recursiveGen = _out369;
                _1859___v161 = _out370;
                _1860_recIdents = _out371;
                _1856_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1856_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.IntoUsize(_1858_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1860_recIdents);
              }
              if ((new BigInteger((_1852_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _1861_class__name;
                _1861_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_1852_dims).Count)));
                r = ((((RAST.__default.dafny__runtime).MSel(_1861_class__name)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1855_typeGen))).MSel((this).placebos__usize)).Apply(_1856_dimExprs);
              } else {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1855_typeGen))).Apply(_1856_dimExprs);
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
          DAST._IExpression _1862_underlying = _source95.dtor_value;
          unmatched95 = false;
          {
            RAST._IExpr _1863_recursiveGen;
            DCOMP._IOwnership _1864___v162;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1865_recIdents;
            RAST._IExpr _out374;
            DCOMP._IOwnership _out375;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out376;
            (this).GenExpr(_1862_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out374, out _out375, out _out376);
            _1863_recursiveGen = _out374;
            _1864___v162 = _out375;
            _1865_recIdents = _out376;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(_1863_recursiveGen);
            readIdents = _1865_recIdents;
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
          DAST._IExpression _1866_underlying = _source95.dtor_value;
          DAST._IType _1867_typ = _source95.dtor_typ;
          unmatched95 = false;
          {
            RAST._IType _1868_tpe;
            RAST._IType _out379;
            _out379 = (this).GenType(_1867_typ, DCOMP.GenTypeContext.@default());
            _1868_tpe = _out379;
            RAST._IExpr _1869_recursiveGen;
            DCOMP._IOwnership _1870___v163;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1871_recIdents;
            RAST._IExpr _out380;
            DCOMP._IOwnership _out381;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out382;
            (this).GenExpr(_1866_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out380, out _out381, out _out382);
            _1869_recursiveGen = _out380;
            _1870___v163 = _out381;
            _1871_recIdents = _out382;
            readIdents = _1871_recIdents;
            if ((_1868_tpe).IsObjectOrPointer()) {
              RAST._IType _1872_t;
              _1872_t = (_1868_tpe).ObjectOrPointerUnderlying();
              if ((_1872_t).is_Array) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).array__construct)).Apply1(_1869_recursiveGen);
              } else if ((_1872_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _1873_c;
                _1873_c = (_1872_t).MultiArrayClass();
                r = (((RAST.__default.dafny__runtime).MSel(_1873_c)).MSel((this).array__construct)).Apply1(_1869_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_1868_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_1868_tpe)._ToString(DCOMP.__default.IND)));
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
          DAST._IResolvedType _1874_datatypeType = _source95.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1875_typeArgs = _source95.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1876_variant = _source95.dtor_variant;
          bool _1877_isCo = _source95.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1878_values = _source95.dtor_contents;
          unmatched95 = false;
          {
            RAST._IExpr _out385;
            _out385 = DCOMP.COMP.GenPathExpr((_1874_datatypeType).dtor_path);
            r = _out385;
            Dafny.ISequence<RAST._IType> _1879_genTypeArgs;
            _1879_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi43 = new BigInteger((_1875_typeArgs).Count);
            for (BigInteger _1880_i = BigInteger.Zero; _1880_i < _hi43; _1880_i++) {
              RAST._IType _1881_typeExpr;
              RAST._IType _out386;
              _out386 = (this).GenType((_1875_typeArgs).Select(_1880_i), DCOMP.GenTypeContext.@default());
              _1881_typeExpr = _out386;
              _1879_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1879_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1881_typeExpr));
            }
            if ((new BigInteger((_1875_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1879_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1876_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1882_assignments;
            _1882_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi44 = new BigInteger((_1878_values).Count);
            for (BigInteger _1883_i = BigInteger.Zero; _1883_i < _hi44; _1883_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs67 = (_1878_values).Select(_1883_i);
              Dafny.ISequence<Dafny.Rune> _1884_name = _let_tmp_rhs67.dtor__0;
              DAST._IExpression _1885_value = _let_tmp_rhs67.dtor__1;
              if (_1877_isCo) {
                RAST._IExpr _1886_recursiveGen;
                DCOMP._IOwnership _1887___v164;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1888_recIdents;
                RAST._IExpr _out387;
                DCOMP._IOwnership _out388;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out389;
                (this).GenExpr(_1885_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out387, out _out388, out _out389);
                _1886_recursiveGen = _out387;
                _1887___v164 = _out388;
                _1888_recIdents = _out389;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1888_recIdents);
                Dafny.ISequence<Dafny.Rune> _1889_allReadCloned;
                _1889_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1888_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1890_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1888_recIdents).Elements) {
                    _1890_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1888_recIdents).Contains(_1890_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4380)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1889_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1889_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1890_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1890_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1888_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1888_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1890_next));
                }
                Dafny.ISequence<Dafny.Rune> _1891_wasAssigned;
                _1891_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1889_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1886_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1882_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1882_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1884_name), RAST.Expr.create_RawExpr(_1891_wasAssigned))));
              } else {
                RAST._IExpr _1892_recursiveGen;
                DCOMP._IOwnership _1893___v165;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1894_recIdents;
                RAST._IExpr _out390;
                DCOMP._IOwnership _out391;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out392;
                (this).GenExpr(_1885_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out390, out _out391, out _out392);
                _1892_recursiveGen = _out390;
                _1893___v165 = _out391;
                _1894_recIdents = _out392;
                _1882_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1882_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1884_name), _1892_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1894_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1882_assignments);
            if ((this).IsRcWrapped((_1874_datatypeType).dtor_attributes)) {
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
          DAST._IExpression _1895_length = _source95.dtor_length;
          DAST._IExpression _1896_expr = _source95.dtor_elem;
          unmatched95 = false;
          {
            RAST._IExpr _1897_recursiveGen;
            DCOMP._IOwnership _1898___v169;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1899_recIdents;
            RAST._IExpr _out398;
            DCOMP._IOwnership _out399;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out400;
            (this).GenExpr(_1896_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out398, out _out399, out _out400);
            _1897_recursiveGen = _out398;
            _1898___v169 = _out399;
            _1899_recIdents = _out400;
            RAST._IExpr _1900_lengthGen;
            DCOMP._IOwnership _1901___v170;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1902_lengthIdents;
            RAST._IExpr _out401;
            DCOMP._IOwnership _out402;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
            (this).GenExpr(_1895_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out401, out _out402, out _out403);
            _1900_lengthGen = _out401;
            _1901___v170 = _out402;
            _1902_lengthIdents = _out403;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1897_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1900_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1899_recIdents, _1902_lengthIdents);
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
          Dafny.ISequence<DAST._IExpression> _1903_exprs = _source95.dtor_elements;
          DAST._IType _1904_typ = _source95.dtor_typ;
          unmatched95 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1905_genTpe;
            RAST._IType _out406;
            _out406 = (this).GenType(_1904_typ, DCOMP.GenTypeContext.@default());
            _1905_genTpe = _out406;
            BigInteger _1906_i;
            _1906_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1907_args;
            _1907_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1906_i) < (new BigInteger((_1903_exprs).Count))) {
              RAST._IExpr _1908_recursiveGen;
              DCOMP._IOwnership _1909___v171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1910_recIdents;
              RAST._IExpr _out407;
              DCOMP._IOwnership _out408;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
              (this).GenExpr((_1903_exprs).Select(_1906_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out407, out _out408, out _out409);
              _1908_recursiveGen = _out407;
              _1909___v171 = _out408;
              _1910_recIdents = _out409;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1910_recIdents);
              _1907_args = Dafny.Sequence<RAST._IExpr>.Concat(_1907_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1908_recursiveGen));
              _1906_i = (_1906_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_1907_args);
            if ((new BigInteger((_1907_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1905_genTpe));
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
          Dafny.ISequence<DAST._IExpression> _1911_exprs = _source95.dtor_elements;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1912_generatedValues;
            _1912_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1913_i;
            _1913_i = BigInteger.Zero;
            while ((_1913_i) < (new BigInteger((_1911_exprs).Count))) {
              RAST._IExpr _1914_recursiveGen;
              DCOMP._IOwnership _1915___v172;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1916_recIdents;
              RAST._IExpr _out412;
              DCOMP._IOwnership _out413;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out414;
              (this).GenExpr((_1911_exprs).Select(_1913_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out412, out _out413, out _out414);
              _1914_recursiveGen = _out412;
              _1915___v172 = _out413;
              _1916_recIdents = _out414;
              _1912_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1912_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1914_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1916_recIdents);
              _1913_i = (_1913_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_1912_generatedValues);
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
          Dafny.ISequence<DAST._IExpression> _1917_exprs = _source95.dtor_elements;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1918_generatedValues;
            _1918_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1919_i;
            _1919_i = BigInteger.Zero;
            while ((_1919_i) < (new BigInteger((_1917_exprs).Count))) {
              RAST._IExpr _1920_recursiveGen;
              DCOMP._IOwnership _1921___v173;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1922_recIdents;
              RAST._IExpr _out417;
              DCOMP._IOwnership _out418;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out419;
              (this).GenExpr((_1917_exprs).Select(_1919_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out417, out _out418, out _out419);
              _1920_recursiveGen = _out417;
              _1921___v173 = _out418;
              _1922_recIdents = _out419;
              _1918_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1918_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1920_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1922_recIdents);
              _1919_i = (_1919_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_1918_generatedValues);
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
          DAST._IExpression _1923_expr = _source95.dtor_ToMultiset_a0;
          unmatched95 = false;
          {
            RAST._IExpr _1924_recursiveGen;
            DCOMP._IOwnership _1925___v174;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1926_recIdents;
            RAST._IExpr _out422;
            DCOMP._IOwnership _out423;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out424;
            (this).GenExpr(_1923_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out422, out _out423, out _out424);
            _1924_recursiveGen = _out422;
            _1925___v174 = _out423;
            _1926_recIdents = _out424;
            r = ((_1924_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _1926_recIdents;
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
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1927_mapElems = _source95.dtor_mapElems;
          unmatched95 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1928_generatedValues;
            _1928_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1929_i;
            _1929_i = BigInteger.Zero;
            while ((_1929_i) < (new BigInteger((_1927_mapElems).Count))) {
              RAST._IExpr _1930_recursiveGenKey;
              DCOMP._IOwnership _1931___v175;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1932_recIdentsKey;
              RAST._IExpr _out427;
              DCOMP._IOwnership _out428;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out429;
              (this).GenExpr(((_1927_mapElems).Select(_1929_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out427, out _out428, out _out429);
              _1930_recursiveGenKey = _out427;
              _1931___v175 = _out428;
              _1932_recIdentsKey = _out429;
              RAST._IExpr _1933_recursiveGenValue;
              DCOMP._IOwnership _1934___v176;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1935_recIdentsValue;
              RAST._IExpr _out430;
              DCOMP._IOwnership _out431;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out432;
              (this).GenExpr(((_1927_mapElems).Select(_1929_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out430, out _out431, out _out432);
              _1933_recursiveGenValue = _out430;
              _1934___v176 = _out431;
              _1935_recIdentsValue = _out432;
              _1928_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1928_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1930_recursiveGenKey, _1933_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1932_recIdentsKey), _1935_recIdentsValue);
              _1929_i = (_1929_i) + (BigInteger.One);
            }
            _1929_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1936_arguments;
            _1936_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1929_i) < (new BigInteger((_1928_generatedValues).Count))) {
              RAST._IExpr _1937_genKey;
              _1937_genKey = ((_1928_generatedValues).Select(_1929_i)).dtor__0;
              RAST._IExpr _1938_genValue;
              _1938_genValue = ((_1928_generatedValues).Select(_1929_i)).dtor__1;
              _1936_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1936_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1937_genKey, _1938_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _1929_i = (_1929_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_1936_arguments);
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
          DAST._IExpression _1939_expr = _source95.dtor_expr;
          DAST._IExpression _1940_index = _source95.dtor_indexExpr;
          DAST._IExpression _1941_value = _source95.dtor_value;
          unmatched95 = false;
          {
            RAST._IExpr _1942_exprR;
            DCOMP._IOwnership _1943___v177;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1944_exprIdents;
            RAST._IExpr _out435;
            DCOMP._IOwnership _out436;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out437;
            (this).GenExpr(_1939_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out435, out _out436, out _out437);
            _1942_exprR = _out435;
            _1943___v177 = _out436;
            _1944_exprIdents = _out437;
            RAST._IExpr _1945_indexR;
            DCOMP._IOwnership _1946_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1947_indexIdents;
            RAST._IExpr _out438;
            DCOMP._IOwnership _out439;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out440;
            (this).GenExpr(_1940_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out438, out _out439, out _out440);
            _1945_indexR = _out438;
            _1946_indexOwnership = _out439;
            _1947_indexIdents = _out440;
            RAST._IExpr _1948_valueR;
            DCOMP._IOwnership _1949_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1950_valueIdents;
            RAST._IExpr _out441;
            DCOMP._IOwnership _out442;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out443;
            (this).GenExpr(_1941_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out441, out _out442, out _out443);
            _1948_valueR = _out441;
            _1949_valueOwnership = _out442;
            _1950_valueIdents = _out443;
            r = ((_1942_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1945_indexR, _1948_valueR));
            RAST._IExpr _out444;
            DCOMP._IOwnership _out445;
            (this).FromOwned(r, expectedOwnership, out _out444, out _out445);
            r = _out444;
            resultingOwnership = _out445;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1944_exprIdents, _1947_indexIdents), _1950_valueIdents);
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_MapUpdate) {
          DAST._IExpression _1951_expr = _source95.dtor_expr;
          DAST._IExpression _1952_index = _source95.dtor_indexExpr;
          DAST._IExpression _1953_value = _source95.dtor_value;
          unmatched95 = false;
          {
            RAST._IExpr _1954_exprR;
            DCOMP._IOwnership _1955___v178;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1956_exprIdents;
            RAST._IExpr _out446;
            DCOMP._IOwnership _out447;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out448;
            (this).GenExpr(_1951_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out446, out _out447, out _out448);
            _1954_exprR = _out446;
            _1955___v178 = _out447;
            _1956_exprIdents = _out448;
            RAST._IExpr _1957_indexR;
            DCOMP._IOwnership _1958_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1959_indexIdents;
            RAST._IExpr _out449;
            DCOMP._IOwnership _out450;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
            (this).GenExpr(_1952_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out449, out _out450, out _out451);
            _1957_indexR = _out449;
            _1958_indexOwnership = _out450;
            _1959_indexIdents = _out451;
            RAST._IExpr _1960_valueR;
            DCOMP._IOwnership _1961_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1962_valueIdents;
            RAST._IExpr _out452;
            DCOMP._IOwnership _out453;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out454;
            (this).GenExpr(_1953_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out452, out _out453, out _out454);
            _1960_valueR = _out452;
            _1961_valueOwnership = _out453;
            _1962_valueIdents = _out454;
            r = ((_1954_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1957_indexR, _1960_valueR));
            RAST._IExpr _out455;
            DCOMP._IOwnership _out456;
            (this).FromOwned(r, expectedOwnership, out _out455, out _out456);
            r = _out455;
            resultingOwnership = _out456;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1956_exprIdents, _1959_indexIdents), _1962_valueIdents);
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
                Dafny.ISequence<Dafny.Rune> _1963_id = _source96.dtor_rSelfName;
                DAST._IType _1964_dafnyType = _source96.dtor_dafnyType;
                unmatched96 = false;
                {
                  RAST._IExpr _out457;
                  DCOMP._IOwnership _out458;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out459;
                  (this).GenIdent(_1963_id, selfIdent, env, expectedOwnership, out _out457, out _out458, out _out459);
                  r = _out457;
                  resultingOwnership = _out458;
                  readIdents = _out459;
                }
              }
            }
            if (unmatched96) {
              DCOMP._ISelfInfo _1965_None = _source96;
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
          DAST._IExpression _1966_cond = _source95.dtor_cond;
          DAST._IExpression _1967_t = _source95.dtor_thn;
          DAST._IExpression _1968_f = _source95.dtor_els;
          unmatched95 = false;
          {
            RAST._IExpr _1969_cond;
            DCOMP._IOwnership _1970___v179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1971_recIdentsCond;
            RAST._IExpr _out462;
            DCOMP._IOwnership _out463;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out464;
            (this).GenExpr(_1966_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out462, out _out463, out _out464);
            _1969_cond = _out462;
            _1970___v179 = _out463;
            _1971_recIdentsCond = _out464;
            RAST._IExpr _1972_fExpr;
            DCOMP._IOwnership _1973_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1974_recIdentsF;
            RAST._IExpr _out465;
            DCOMP._IOwnership _out466;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out467;
            (this).GenExpr(_1968_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out465, out _out466, out _out467);
            _1972_fExpr = _out465;
            _1973_fOwned = _out466;
            _1974_recIdentsF = _out467;
            RAST._IExpr _1975_tExpr;
            DCOMP._IOwnership _1976___v180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1977_recIdentsT;
            RAST._IExpr _out468;
            DCOMP._IOwnership _out469;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out470;
            (this).GenExpr(_1967_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out468, out _out469, out _out470);
            _1975_tExpr = _out468;
            _1976___v180 = _out469;
            _1977_recIdentsT = _out470;
            r = RAST.Expr.create_IfExpr(_1969_cond, _1975_tExpr, _1972_fExpr);
            RAST._IExpr _out471;
            DCOMP._IOwnership _out472;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out471, out _out472);
            r = _out471;
            resultingOwnership = _out472;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1971_recIdentsCond, _1977_recIdentsT), _1974_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source95.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _1978_e = _source95.dtor_expr;
            DAST.Format._IUnaryOpFormat _1979_format = _source95.dtor_format1;
            unmatched95 = false;
            {
              RAST._IExpr _1980_recursiveGen;
              DCOMP._IOwnership _1981___v181;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1982_recIdents;
              RAST._IExpr _out473;
              DCOMP._IOwnership _out474;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out475;
              (this).GenExpr(_1978_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out473, out _out474, out _out475);
              _1980_recursiveGen = _out473;
              _1981___v181 = _out474;
              _1982_recIdents = _out475;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _1980_recursiveGen, _1979_format);
              RAST._IExpr _out476;
              DCOMP._IOwnership _out477;
              (this).FromOwned(r, expectedOwnership, out _out476, out _out477);
              r = _out476;
              resultingOwnership = _out477;
              readIdents = _1982_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source95.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _1983_e = _source95.dtor_expr;
            DAST.Format._IUnaryOpFormat _1984_format = _source95.dtor_format1;
            unmatched95 = false;
            {
              RAST._IExpr _1985_recursiveGen;
              DCOMP._IOwnership _1986___v182;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1987_recIdents;
              RAST._IExpr _out478;
              DCOMP._IOwnership _out479;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out480;
              (this).GenExpr(_1983_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out478, out _out479, out _out480);
              _1985_recursiveGen = _out478;
              _1986___v182 = _out479;
              _1987_recIdents = _out480;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _1985_recursiveGen, _1984_format);
              RAST._IExpr _out481;
              DCOMP._IOwnership _out482;
              (this).FromOwned(r, expectedOwnership, out _out481, out _out482);
              r = _out481;
              resultingOwnership = _out482;
              readIdents = _1987_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source95.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _1988_e = _source95.dtor_expr;
            DAST.Format._IUnaryOpFormat _1989_format = _source95.dtor_format1;
            unmatched95 = false;
            {
              RAST._IExpr _1990_recursiveGen;
              DCOMP._IOwnership _1991_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1992_recIdents;
              RAST._IExpr _out483;
              DCOMP._IOwnership _out484;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out485;
              (this).GenExpr(_1988_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out483, out _out484, out _out485);
              _1990_recursiveGen = _out483;
              _1991_recOwned = _out484;
              _1992_recIdents = _out485;
              r = ((_1990_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out486;
              DCOMP._IOwnership _out487;
              (this).FromOwned(r, expectedOwnership, out _out486, out _out487);
              r = _out486;
              resultingOwnership = _out487;
              readIdents = _1992_recIdents;
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
          DAST._IExpression _1993_expr = _source95.dtor_expr;
          DAST._IType _1994_exprType = _source95.dtor_exprType;
          BigInteger _1995_dim = _source95.dtor_dim;
          bool _1996_native = _source95.dtor_native;
          unmatched95 = false;
          {
            RAST._IExpr _1997_recursiveGen;
            DCOMP._IOwnership _1998___v187;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1999_recIdents;
            RAST._IExpr _out491;
            DCOMP._IOwnership _out492;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out493;
            (this).GenExpr(_1993_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out491, out _out492, out _out493);
            _1997_recursiveGen = _out491;
            _1998___v187 = _out492;
            _1999_recIdents = _out493;
            RAST._IType _2000_arrayType;
            RAST._IType _out494;
            _out494 = (this).GenType(_1994_exprType, DCOMP.GenTypeContext.@default());
            _2000_arrayType = _out494;
            if (!((_2000_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _2001_msg;
              _2001_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_2000_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2001_msg);
              r = RAST.Expr.create_RawExpr(_2001_msg);
            } else {
              RAST._IType _2002_underlying;
              _2002_underlying = (_2000_arrayType).ObjectOrPointerUnderlying();
              if (((_1995_dim).Sign == 0) && ((_2002_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_1997_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_1995_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_1997_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = ((((this).read__macro).Apply1(_1997_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("length"), Std.Strings.__default.OfNat(_1995_dim)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_usize")))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                }
              }
              if (!(_1996_native)) {
                r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(r);
              }
            }
            RAST._IExpr _out495;
            DCOMP._IOwnership _out496;
            (this).FromOwned(r, expectedOwnership, out _out495, out _out496);
            r = _out495;
            resultingOwnership = _out496;
            readIdents = _1999_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_MapKeys) {
          DAST._IExpression _2003_expr = _source95.dtor_expr;
          unmatched95 = false;
          {
            RAST._IExpr _2004_recursiveGen;
            DCOMP._IOwnership _2005___v188;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2006_recIdents;
            RAST._IExpr _out497;
            DCOMP._IOwnership _out498;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out499;
            (this).GenExpr(_2003_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out497, out _out498, out _out499);
            _2004_recursiveGen = _out497;
            _2005___v188 = _out498;
            _2006_recIdents = _out499;
            readIdents = _2006_recIdents;
            r = ((_2004_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
          DAST._IExpression _2007_expr = _source95.dtor_expr;
          unmatched95 = false;
          {
            RAST._IExpr _2008_recursiveGen;
            DCOMP._IOwnership _2009___v189;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2010_recIdents;
            RAST._IExpr _out502;
            DCOMP._IOwnership _out503;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out504;
            (this).GenExpr(_2007_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out502, out _out503, out _out504);
            _2008_recursiveGen = _out502;
            _2009___v189 = _out503;
            _2010_recIdents = _out504;
            readIdents = _2010_recIdents;
            r = ((_2008_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
          DAST._IExpression _2011_on = _source95.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2012_field = _source95.dtor_field;
          bool _2013_isDatatype = _source95.dtor_onDatatype;
          bool _2014_isStatic = _source95.dtor_isStatic;
          BigInteger _2015_arity = _source95.dtor_arity;
          unmatched95 = false;
          {
            RAST._IExpr _2016_onExpr;
            DCOMP._IOwnership _2017_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2018_recIdents;
            RAST._IExpr _out507;
            DCOMP._IOwnership _out508;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out509;
            (this).GenExpr(_2011_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out507, out _out508, out _out509);
            _2016_onExpr = _out507;
            _2017_onOwned = _out508;
            _2018_recIdents = _out509;
            Dafny.ISequence<Dafny.Rune> _2019_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _2020_onString;
            _2020_onString = (_2016_onExpr)._ToString(DCOMP.__default.IND);
            if (_2014_isStatic) {
              _2019_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2020_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_2012_field));
            } else {
              _2019_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _2019_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2019_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2020_onString), ((object.Equals(_2017_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _2021_args;
              _2021_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _2022_i;
              _2022_i = BigInteger.Zero;
              while ((_2022_i) < (_2015_arity)) {
                if ((_2022_i).Sign == 1) {
                  _2021_args = Dafny.Sequence<Dafny.Rune>.Concat(_2021_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _2021_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2021_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_2022_i));
                _2022_i = (_2022_i) + (BigInteger.One);
              }
              _2019_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2019_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2021_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _2019_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2019_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_2012_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2021_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _2019_s = Dafny.Sequence<Dafny.Rune>.Concat(_2019_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _2019_s = Dafny.Sequence<Dafny.Rune>.Concat(_2019_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _2023_typeShape;
            _2023_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _2024_i;
            _2024_i = BigInteger.Zero;
            while ((_2024_i) < (_2015_arity)) {
              if ((_2024_i).Sign == 1) {
                _2023_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2023_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2023_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2023_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _2024_i = (_2024_i) + (BigInteger.One);
            }
            _2023_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2023_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _2019_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _2019_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _2023_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_2019_s);
            RAST._IExpr _out510;
            DCOMP._IOwnership _out511;
            (this).FromOwned(r, expectedOwnership, out _out510, out _out511);
            r = _out510;
            resultingOwnership = _out511;
            readIdents = _2018_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Select) {
          DAST._IExpression expr0 = _source95.dtor_expr;
          if (expr0.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2025_c = expr0.dtor_Companion_a0;
            Dafny.ISequence<DAST._IType> _2026_typeArgs = expr0.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _2027_field = _source95.dtor_field;
            bool _2028_isConstant = _source95.dtor_isConstant;
            bool _2029_isDatatype = _source95.dtor_onDatatype;
            DAST._IType _2030_fieldType = _source95.dtor_fieldType;
            unmatched95 = false;
            {
              RAST._IExpr _2031_onExpr;
              DCOMP._IOwnership _2032_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2033_recIdents;
              RAST._IExpr _out512;
              DCOMP._IOwnership _out513;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out514;
              (this).GenExpr(DAST.Expression.create_Companion(_2025_c, _2026_typeArgs), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out512, out _out513, out _out514);
              _2031_onExpr = _out512;
              _2032_onOwned = _out513;
              _2033_recIdents = _out514;
              r = ((_2031_onExpr).MSel(DCOMP.__default.escapeName(_2027_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out515;
              DCOMP._IOwnership _out516;
              (this).FromOwned(r, expectedOwnership, out _out515, out _out516);
              r = _out515;
              resultingOwnership = _out516;
              readIdents = _2033_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Select) {
          DAST._IExpression _2034_on = _source95.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2035_field = _source95.dtor_field;
          bool _2036_isConstant = _source95.dtor_isConstant;
          bool _2037_isDatatype = _source95.dtor_onDatatype;
          DAST._IType _2038_fieldType = _source95.dtor_fieldType;
          unmatched95 = false;
          {
            if (_2037_isDatatype) {
              RAST._IExpr _2039_onExpr;
              DCOMP._IOwnership _2040_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2041_recIdents;
              RAST._IExpr _out517;
              DCOMP._IOwnership _out518;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out519;
              (this).GenExpr(_2034_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out517, out _out518, out _out519);
              _2039_onExpr = _out517;
              _2040_onOwned = _out518;
              _2041_recIdents = _out519;
              r = ((_2039_onExpr).Sel(DCOMP.__default.escapeName(_2035_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _2042_typ;
              RAST._IType _out520;
              _out520 = (this).GenType(_2038_fieldType, DCOMP.GenTypeContext.@default());
              _2042_typ = _out520;
              RAST._IExpr _out521;
              DCOMP._IOwnership _out522;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out521, out _out522);
              r = _out521;
              resultingOwnership = _out522;
              readIdents = _2041_recIdents;
            } else {
              RAST._IExpr _2043_onExpr;
              DCOMP._IOwnership _2044_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2045_recIdents;
              RAST._IExpr _out523;
              DCOMP._IOwnership _out524;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
              (this).GenExpr(_2034_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out523, out _out524, out _out525);
              _2043_onExpr = _out523;
              _2044_onOwned = _out524;
              _2045_recIdents = _out525;
              r = _2043_onExpr;
              if (!object.Equals(_2043_onExpr, RAST.__default.self)) {
                RAST._IExpr _source97 = _2043_onExpr;
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
              r = (r).Sel(DCOMP.__default.escapeName(_2035_field));
              if (_2036_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out526;
              DCOMP._IOwnership _out527;
              (this).FromOwned(r, expectedOwnership, out _out526, out _out527);
              r = _out526;
              resultingOwnership = _out527;
              readIdents = _2045_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Index) {
          DAST._IExpression _2046_on = _source95.dtor_expr;
          DAST._ICollKind _2047_collKind = _source95.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2048_indices = _source95.dtor_indices;
          unmatched95 = false;
          {
            RAST._IExpr _2049_onExpr;
            DCOMP._IOwnership _2050_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2051_recIdents;
            RAST._IExpr _out528;
            DCOMP._IOwnership _out529;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out530;
            (this).GenExpr(_2046_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out528, out _out529, out _out530);
            _2049_onExpr = _out528;
            _2050_onOwned = _out529;
            _2051_recIdents = _out530;
            readIdents = _2051_recIdents;
            r = _2049_onExpr;
            bool _2052_hadArray;
            _2052_hadArray = false;
            if (object.Equals(_2047_collKind, DAST.CollKind.create_Array())) {
              r = ((this).read__macro).Apply1(r);
              _2052_hadArray = true;
              if ((new BigInteger((_2048_indices).Count)) > (BigInteger.One)) {
                r = (r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
              }
            }
            BigInteger _hi45 = new BigInteger((_2048_indices).Count);
            for (BigInteger _2053_i = BigInteger.Zero; _2053_i < _hi45; _2053_i++) {
              if (object.Equals(_2047_collKind, DAST.CollKind.create_Array())) {
                RAST._IExpr _2054_idx;
                DCOMP._IOwnership _2055_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2056_recIdentsIdx;
                RAST._IExpr _out531;
                DCOMP._IOwnership _out532;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out533;
                (this).GenExpr((_2048_indices).Select(_2053_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out531, out _out532, out _out533);
                _2054_idx = _out531;
                _2055_idxOwned = _out532;
                _2056_recIdentsIdx = _out533;
                _2054_idx = RAST.__default.IntoUsize(_2054_idx);
                r = RAST.Expr.create_SelectIndex(r, _2054_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2056_recIdentsIdx);
              } else {
                RAST._IExpr _2057_idx;
                DCOMP._IOwnership _2058_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2059_recIdentsIdx;
                RAST._IExpr _out534;
                DCOMP._IOwnership _out535;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out536;
                (this).GenExpr((_2048_indices).Select(_2053_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out534, out _out535, out _out536);
                _2057_idx = _out534;
                _2058_idxOwned = _out535;
                _2059_recIdentsIdx = _out536;
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_2057_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2059_recIdentsIdx);
              }
            }
            if (_2052_hadArray) {
              r = (r).Clone();
            }
            RAST._IExpr _out537;
            DCOMP._IOwnership _out538;
            (this).FromOwned(r, expectedOwnership, out _out537, out _out538);
            r = _out537;
            resultingOwnership = _out538;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_IndexRange) {
          DAST._IExpression _2060_on = _source95.dtor_expr;
          bool _2061_isArray = _source95.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _2062_low = _source95.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _2063_high = _source95.dtor_high;
          unmatched95 = false;
          {
            RAST._IExpr _2064_onExpr;
            DCOMP._IOwnership _2065_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2066_recIdents;
            RAST._IExpr _out539;
            DCOMP._IOwnership _out540;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
            (this).GenExpr(_2060_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out539, out _out540, out _out541);
            _2064_onExpr = _out539;
            _2065_onOwned = _out540;
            _2066_recIdents = _out541;
            readIdents = _2066_recIdents;
            Dafny.ISequence<Dafny.Rune> _2067_methodName;
            _2067_methodName = (((_2062_low).is_Some) ? ((((_2063_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_2063_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _2068_arguments;
            _2068_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source98 = _2062_low;
            bool unmatched98 = true;
            if (unmatched98) {
              if (_source98.is_Some) {
                DAST._IExpression _2069_l = _source98.dtor_value;
                unmatched98 = false;
                {
                  RAST._IExpr _2070_lExpr;
                  DCOMP._IOwnership _2071___v192;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2072_recIdentsL;
                  RAST._IExpr _out542;
                  DCOMP._IOwnership _out543;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out544;
                  (this).GenExpr(_2069_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out542, out _out543, out _out544);
                  _2070_lExpr = _out542;
                  _2071___v192 = _out543;
                  _2072_recIdentsL = _out544;
                  _2068_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2068_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2070_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2072_recIdentsL);
                }
              }
            }
            if (unmatched98) {
              unmatched98 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source99 = _2063_high;
            bool unmatched99 = true;
            if (unmatched99) {
              if (_source99.is_Some) {
                DAST._IExpression _2073_h = _source99.dtor_value;
                unmatched99 = false;
                {
                  RAST._IExpr _2074_hExpr;
                  DCOMP._IOwnership _2075___v193;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2076_recIdentsH;
                  RAST._IExpr _out545;
                  DCOMP._IOwnership _out546;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out547;
                  (this).GenExpr(_2073_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out545, out _out546, out _out547);
                  _2074_hExpr = _out545;
                  _2075___v193 = _out546;
                  _2076_recIdentsH = _out547;
                  _2068_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2068_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2074_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2076_recIdentsH);
                }
              }
            }
            if (unmatched99) {
              unmatched99 = false;
            }
            r = _2064_onExpr;
            if (_2061_isArray) {
              if (!(_2067_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _2067_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2067_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _2067_methodName))).Apply(_2068_arguments);
            } else {
              if (!(_2067_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_2067_methodName)).Apply(_2068_arguments);
              }
            }
            RAST._IExpr _out548;
            DCOMP._IOwnership _out549;
            (this).FromOwned(r, expectedOwnership, out _out548, out _out549);
            r = _out548;
            resultingOwnership = _out549;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_TupleSelect) {
          DAST._IExpression _2077_on = _source95.dtor_expr;
          BigInteger _2078_idx = _source95.dtor_index;
          DAST._IType _2079_fieldType = _source95.dtor_fieldType;
          unmatched95 = false;
          {
            RAST._IExpr _2080_onExpr;
            DCOMP._IOwnership _2081_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2082_recIdents;
            RAST._IExpr _out550;
            DCOMP._IOwnership _out551;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out552;
            (this).GenExpr(_2077_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out550, out _out551, out _out552);
            _2080_onExpr = _out550;
            _2081_onOwnership = _out551;
            _2082_recIdents = _out552;
            Dafny.ISequence<Dafny.Rune> _2083_selName;
            _2083_selName = Std.Strings.__default.OfNat(_2078_idx);
            DAST._IType _source100 = _2079_fieldType;
            bool unmatched100 = true;
            if (unmatched100) {
              if (_source100.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2084_tps = _source100.dtor_Tuple_a0;
                unmatched100 = false;
                if (((_2079_fieldType).is_Tuple) && ((new BigInteger((_2084_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _2083_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2083_selName);
                }
              }
            }
            if (unmatched100) {
              unmatched100 = false;
            }
            r = ((_2080_onExpr).Sel(_2083_selName)).Clone();
            RAST._IExpr _out553;
            DCOMP._IOwnership _out554;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out553, out _out554);
            r = _out553;
            resultingOwnership = _out554;
            readIdents = _2082_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Call) {
          DAST._IExpression _2085_on = _source95.dtor_on;
          DAST._ICallName _2086_name = _source95.dtor_callName;
          Dafny.ISequence<DAST._IType> _2087_typeArgs = _source95.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2088_args = _source95.dtor_args;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2089_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2090_recIdents;
            Dafny.ISequence<RAST._IType> _2091_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _2092_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out555;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out556;
            Dafny.ISequence<RAST._IType> _out557;
            Std.Wrappers._IOption<DAST._IResolvedType> _out558;
            (this).GenArgs(selfIdent, _2086_name, _2087_typeArgs, _2088_args, env, out _out555, out _out556, out _out557, out _out558);
            _2089_argExprs = _out555;
            _2090_recIdents = _out556;
            _2091_typeExprs = _out557;
            _2092_fullNameQualifier = _out558;
            readIdents = _2090_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source101 = _2092_fullNameQualifier;
            bool unmatched101 = true;
            if (unmatched101) {
              if (_source101.is_Some) {
                DAST._IResolvedType value11 = _source101.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2093_path = value11.dtor_path;
                Dafny.ISequence<DAST._IType> _2094_onTypeArgs = value11.dtor_typeArgs;
                DAST._IResolvedTypeBase _2095_base = value11.dtor_kind;
                unmatched101 = false;
                RAST._IExpr _2096_fullPath;
                RAST._IExpr _out559;
                _out559 = DCOMP.COMP.GenPathExpr(_2093_path);
                _2096_fullPath = _out559;
                Dafny.ISequence<RAST._IType> _2097_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out560;
                _out560 = (this).GenTypeArgs(_2094_onTypeArgs, DCOMP.GenTypeContext.@default());
                _2097_onTypeExprs = _out560;
                RAST._IExpr _2098_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _2099_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2100_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_2095_base).is_Trait) || ((_2095_base).is_Class)) {
                  RAST._IExpr _out561;
                  DCOMP._IOwnership _out562;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out563;
                  (this).GenExpr(_2085_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out561, out _out562, out _out563);
                  _2098_onExpr = _out561;
                  _2099_recOwnership = _out562;
                  _2100_recIdents = _out563;
                  _2098_onExpr = ((this).read__macro).Apply1(_2098_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2100_recIdents);
                } else {
                  RAST._IExpr _out564;
                  DCOMP._IOwnership _out565;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out566;
                  (this).GenExpr(_2085_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out564, out _out565, out _out566);
                  _2098_onExpr = _out564;
                  _2099_recOwnership = _out565;
                  _2100_recIdents = _out566;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2100_recIdents);
                }
                r = ((((_2096_fullPath).ApplyType(_2097_onTypeExprs)).MSel(DCOMP.__default.escapeName((_2086_name).dtor_name))).ApplyType(_2091_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_2098_onExpr), _2089_argExprs));
                RAST._IExpr _out567;
                DCOMP._IOwnership _out568;
                (this).FromOwned(r, expectedOwnership, out _out567, out _out568);
                r = _out567;
                resultingOwnership = _out568;
              }
            }
            if (unmatched101) {
              unmatched101 = false;
              RAST._IExpr _2101_onExpr;
              DCOMP._IOwnership _2102___v199;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2103_recIdents;
              RAST._IExpr _out569;
              DCOMP._IOwnership _out570;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out571;
              (this).GenExpr(_2085_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out569, out _out570, out _out571);
              _2101_onExpr = _out569;
              _2102___v199 = _out570;
              _2103_recIdents = _out571;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2103_recIdents);
              Dafny.ISequence<Dafny.Rune> _2104_renderedName;
              _2104_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
                DAST._ICallName _source102 = _2086_name;
                bool unmatched102 = true;
                if (unmatched102) {
                  if (_source102.is_CallName) {
                    Dafny.ISequence<Dafny.Rune> _2105_ident = _source102.dtor_name;
                    unmatched102 = false;
                    return DCOMP.__default.escapeName(_2105_ident);
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
              DAST._IExpression _source103 = _2085_on;
              bool unmatched103 = true;
              if (unmatched103) {
                if (_source103.is_Companion) {
                  unmatched103 = false;
                  {
                    _2101_onExpr = (_2101_onExpr).MSel(_2104_renderedName);
                  }
                }
              }
              if (unmatched103) {
                unmatched103 = false;
                {
                  if (!object.Equals(_2101_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source104 = _2086_name;
                    bool unmatched104 = true;
                    if (unmatched104) {
                      if (_source104.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType2 = _source104.dtor_onType;
                        if (onType2.is_Some) {
                          DAST._IType _2106_tpe = onType2.dtor_value;
                          unmatched104 = false;
                          RAST._IType _2107_typ;
                          RAST._IType _out572;
                          _out572 = (this).GenType(_2106_tpe, DCOMP.GenTypeContext.@default());
                          _2107_typ = _out572;
                          if ((_2107_typ).IsObjectOrPointer()) {
                            _2101_onExpr = ((this).read__macro).Apply1(_2101_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched104) {
                      unmatched104 = false;
                    }
                  }
                  _2101_onExpr = (_2101_onExpr).Sel(_2104_renderedName);
                }
              }
              r = ((_2101_onExpr).ApplyType(_2091_typeExprs)).Apply(_2089_argExprs);
              RAST._IExpr _out573;
              DCOMP._IOwnership _out574;
              (this).FromOwned(r, expectedOwnership, out _out573, out _out574);
              r = _out573;
              resultingOwnership = _out574;
              return ;
            }
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2108_paramsDafny = _source95.dtor_params;
          DAST._IType _2109_retType = _source95.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2110_body = _source95.dtor_body;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IFormal> _2111_params;
            Dafny.ISequence<RAST._IFormal> _out575;
            _out575 = (this).GenParams(_2108_paramsDafny);
            _2111_params = _out575;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2112_paramNames;
            _2112_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2113_paramTypesMap;
            _2113_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi46 = new BigInteger((_2111_params).Count);
            for (BigInteger _2114_i = BigInteger.Zero; _2114_i < _hi46; _2114_i++) {
              Dafny.ISequence<Dafny.Rune> _2115_name;
              _2115_name = ((_2111_params).Select(_2114_i)).dtor_name;
              _2112_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2112_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2115_name));
              _2113_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2113_paramTypesMap, _2115_name, ((_2111_params).Select(_2114_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _2116_subEnv;
            _2116_subEnv = ((env).ToOwned()).merge(DCOMP.Environment.create(_2112_paramNames, _2113_paramTypesMap));
            RAST._IExpr _2117_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2118_recIdents;
            DCOMP._IEnvironment _2119___v210;
            RAST._IExpr _out576;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out577;
            DCOMP._IEnvironment _out578;
            (this).GenStmts(_2110_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _2116_subEnv, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out576, out _out577, out _out578);
            _2117_recursiveGen = _out576;
            _2118_recIdents = _out577;
            _2119___v210 = _out578;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _2118_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2118_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_2120_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll7 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_7 in (_2120_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _2121_name = (Dafny.ISequence<Dafny.Rune>)_compr_7;
                if ((_2120_paramNames).Contains(_2121_name)) {
                  _coll7.Add(_2121_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll7);
            }))())(_2112_paramNames));
            RAST._IExpr _2122_allReadCloned;
            _2122_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_2118_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _2123_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_2118_recIdents).Elements) {
                _2123_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_2118_recIdents).Contains(_2123_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 4855)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_2123_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _2124_selfCloned;
                DCOMP._IOwnership _2125___v211;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2126___v212;
                RAST._IExpr _out579;
                DCOMP._IOwnership _out580;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out581;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out579, out _out580, out _out581);
                _2124_selfCloned = _out579;
                _2125___v211 = _out580;
                _2126___v212 = _out581;
                _2122_allReadCloned = (_2122_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2124_selfCloned)));
              } else if (!((_2112_paramNames).Contains(_2123_next))) {
                RAST._IExpr _2127_copy;
                _2127_copy = (RAST.Expr.create_Identifier(_2123_next)).Clone();
                _2122_allReadCloned = (_2122_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2123_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2127_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2123_next));
              }
              _2118_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2118_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2123_next));
            }
            RAST._IType _2128_retTypeGen;
            RAST._IType _out582;
            _out582 = (this).GenType(_2109_retType, DCOMP.GenTypeContext.InFn());
            _2128_retTypeGen = _out582;
            r = RAST.Expr.create_Block((_2122_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_2111_params, Std.Wrappers.Option<RAST._IType>.create_Some(_2128_retTypeGen), RAST.Expr.create_Block(_2117_recursiveGen)))));
            RAST._IExpr _out583;
            DCOMP._IOwnership _out584;
            (this).FromOwned(r, expectedOwnership, out _out583, out _out584);
            r = _out583;
            resultingOwnership = _out584;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2129_values = _source95.dtor_values;
          DAST._IType _2130_retType = _source95.dtor_retType;
          DAST._IExpression _2131_expr = _source95.dtor_expr;
          unmatched95 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2132_paramNames;
            _2132_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2133_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out585;
            _out585 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2134_value) => {
              return (_2134_value).dtor__0;
            })), _2129_values));
            _2133_paramFormals = _out585;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2135_paramTypes;
            _2135_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2136_paramNamesSet;
            _2136_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi47 = new BigInteger((_2129_values).Count);
            for (BigInteger _2137_i = BigInteger.Zero; _2137_i < _hi47; _2137_i++) {
              Dafny.ISequence<Dafny.Rune> _2138_name;
              _2138_name = (((_2129_values).Select(_2137_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2139_rName;
              _2139_rName = DCOMP.__default.escapeName(_2138_name);
              _2132_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2132_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2139_rName));
              _2135_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2135_paramTypes, _2139_rName, ((_2133_paramFormals).Select(_2137_i)).dtor_tpe);
              _2136_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2136_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2139_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi48 = new BigInteger((_2129_values).Count);
            for (BigInteger _2140_i = BigInteger.Zero; _2140_i < _hi48; _2140_i++) {
              RAST._IType _2141_typeGen;
              RAST._IType _out586;
              _out586 = (this).GenType((((_2129_values).Select(_2140_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.InFn());
              _2141_typeGen = _out586;
              RAST._IExpr _2142_valueGen;
              DCOMP._IOwnership _2143___v213;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2144_recIdents;
              RAST._IExpr _out587;
              DCOMP._IOwnership _out588;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out589;
              (this).GenExpr(((_2129_values).Select(_2140_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out587, out _out588, out _out589);
              _2142_valueGen = _out587;
              _2143___v213 = _out588;
              _2144_recIdents = _out589;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_2129_values).Select(_2140_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2141_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2142_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2144_recIdents);
            }
            DCOMP._IEnvironment _2145_newEnv;
            _2145_newEnv = DCOMP.Environment.create(_2132_paramNames, _2135_paramTypes);
            RAST._IExpr _2146_recGen;
            DCOMP._IOwnership _2147_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2148_recIdents;
            RAST._IExpr _out590;
            DCOMP._IOwnership _out591;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out592;
            (this).GenExpr(_2131_expr, selfIdent, _2145_newEnv, expectedOwnership, out _out590, out _out591, out _out592);
            _2146_recGen = _out590;
            _2147_recOwned = _out591;
            _2148_recIdents = _out592;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2148_recIdents, _2136_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2146_recGen));
            RAST._IExpr _out593;
            DCOMP._IOwnership _out594;
            (this).FromOwnership(r, _2147_recOwned, expectedOwnership, out _out593, out _out594);
            r = _out593;
            resultingOwnership = _out594;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2149_name = _source95.dtor_ident;
          DAST._IType _2150_tpe = _source95.dtor_typ;
          DAST._IExpression _2151_value = _source95.dtor_value;
          DAST._IExpression _2152_iifeBody = _source95.dtor_iifeBody;
          unmatched95 = false;
          {
            RAST._IExpr _2153_valueGen;
            DCOMP._IOwnership _2154___v214;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2155_recIdents;
            RAST._IExpr _out595;
            DCOMP._IOwnership _out596;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out597;
            (this).GenExpr(_2151_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out595, out _out596, out _out597);
            _2153_valueGen = _out595;
            _2154___v214 = _out596;
            _2155_recIdents = _out597;
            readIdents = _2155_recIdents;
            RAST._IType _2156_valueTypeGen;
            RAST._IType _out598;
            _out598 = (this).GenType(_2150_tpe, DCOMP.GenTypeContext.InFn());
            _2156_valueTypeGen = _out598;
            RAST._IExpr _2157_bodyGen;
            DCOMP._IOwnership _2158___v215;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2159_bodyIdents;
            RAST._IExpr _out599;
            DCOMP._IOwnership _out600;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out601;
            (this).GenExpr(_2152_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out599, out _out600, out _out601);
            _2157_bodyGen = _out599;
            _2158___v215 = _out600;
            _2159_bodyIdents = _out601;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2159_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_2149_name)))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_2149_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_2156_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2153_valueGen))).Then(_2157_bodyGen));
            RAST._IExpr _out602;
            DCOMP._IOwnership _out603;
            (this).FromOwned(r, expectedOwnership, out _out602, out _out603);
            r = _out602;
            resultingOwnership = _out603;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Apply) {
          DAST._IExpression _2160_func = _source95.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2161_args = _source95.dtor_args;
          unmatched95 = false;
          {
            RAST._IExpr _2162_funcExpr;
            DCOMP._IOwnership _2163___v216;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2164_recIdents;
            RAST._IExpr _out604;
            DCOMP._IOwnership _out605;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out606;
            (this).GenExpr(_2160_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out604, out _out605, out _out606);
            _2162_funcExpr = _out604;
            _2163___v216 = _out605;
            _2164_recIdents = _out606;
            readIdents = _2164_recIdents;
            Dafny.ISequence<RAST._IExpr> _2165_rArgs;
            _2165_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi49 = new BigInteger((_2161_args).Count);
            for (BigInteger _2166_i = BigInteger.Zero; _2166_i < _hi49; _2166_i++) {
              RAST._IExpr _2167_argExpr;
              DCOMP._IOwnership _2168_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2169_argIdents;
              RAST._IExpr _out607;
              DCOMP._IOwnership _out608;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out609;
              (this).GenExpr((_2161_args).Select(_2166_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out607, out _out608, out _out609);
              _2167_argExpr = _out607;
              _2168_argOwned = _out608;
              _2169_argIdents = _out609;
              _2165_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2165_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2167_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2169_argIdents);
            }
            r = (_2162_funcExpr).Apply(_2165_rArgs);
            RAST._IExpr _out610;
            DCOMP._IOwnership _out611;
            (this).FromOwned(r, expectedOwnership, out _out610, out _out611);
            r = _out610;
            resultingOwnership = _out611;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_TypeTest) {
          DAST._IExpression _2170_on = _source95.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2171_dType = _source95.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2172_variant = _source95.dtor_variant;
          unmatched95 = false;
          {
            RAST._IExpr _2173_exprGen;
            DCOMP._IOwnership _2174___v217;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2175_recIdents;
            RAST._IExpr _out612;
            DCOMP._IOwnership _out613;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out614;
            (this).GenExpr(_2170_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out612, out _out613, out _out614);
            _2173_exprGen = _out612;
            _2174___v217 = _out613;
            _2175_recIdents = _out614;
            RAST._IType _2176_dTypePath;
            RAST._IType _out615;
            _out615 = DCOMP.COMP.GenPath(_2171_dType);
            _2176_dTypePath = _out615;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2173_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_2176_dTypePath).MSel(DCOMP.__default.escapeName(_2172_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out616;
            DCOMP._IOwnership _out617;
            (this).FromOwned(r, expectedOwnership, out _out616, out _out617);
            r = _out616;
            resultingOwnership = _out617;
            readIdents = _2175_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_BoolBoundedPool) {
          unmatched95 = false;
          {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
            RAST._IExpr _out618;
            DCOMP._IOwnership _out619;
            (this).FromOwned(r, expectedOwnership, out _out618, out _out619);
            r = _out618;
            resultingOwnership = _out619;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_SetBoundedPool) {
          DAST._IExpression _2177_of = _source95.dtor_of;
          unmatched95 = false;
          {
            RAST._IExpr _2178_exprGen;
            DCOMP._IOwnership _2179___v218;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2180_recIdents;
            RAST._IExpr _out620;
            DCOMP._IOwnership _out621;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
            (this).GenExpr(_2177_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out620, out _out621, out _out622);
            _2178_exprGen = _out620;
            _2179___v218 = _out621;
            _2180_recIdents = _out622;
            r = ((_2178_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out623;
            DCOMP._IOwnership _out624;
            (this).FromOwned(r, expectedOwnership, out _out623, out _out624);
            r = _out623;
            resultingOwnership = _out624;
            readIdents = _2180_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_SeqBoundedPool) {
          DAST._IExpression _2181_of = _source95.dtor_of;
          bool _2182_includeDuplicates = _source95.dtor_includeDuplicates;
          unmatched95 = false;
          {
            RAST._IExpr _2183_exprGen;
            DCOMP._IOwnership _2184___v219;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2185_recIdents;
            RAST._IExpr _out625;
            DCOMP._IOwnership _out626;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out627;
            (this).GenExpr(_2181_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out625, out _out626, out _out627);
            _2183_exprGen = _out625;
            _2184___v219 = _out626;
            _2185_recIdents = _out627;
            r = ((_2183_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2182_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out628;
            DCOMP._IOwnership _out629;
            (this).FromOwned(r, expectedOwnership, out _out628, out _out629);
            r = _out628;
            resultingOwnership = _out629;
            readIdents = _2185_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_MapBoundedPool) {
          DAST._IExpression _2186_of = _source95.dtor_of;
          unmatched95 = false;
          {
            RAST._IExpr _2187_exprGen;
            DCOMP._IOwnership _2188___v220;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2189_recIdents;
            RAST._IExpr _out630;
            DCOMP._IOwnership _out631;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out632;
            (this).GenExpr(_2186_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out630, out _out631, out _out632);
            _2187_exprGen = _out630;
            _2188___v220 = _out631;
            _2189_recIdents = _out632;
            r = ((((_2187_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2189_recIdents;
            RAST._IExpr _out633;
            DCOMP._IOwnership _out634;
            (this).FromOwned(r, expectedOwnership, out _out633, out _out634);
            r = _out633;
            resultingOwnership = _out634;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_IntRange) {
          DAST._IExpression _2190_lo = _source95.dtor_lo;
          DAST._IExpression _2191_hi = _source95.dtor_hi;
          bool _2192_up = _source95.dtor_up;
          unmatched95 = false;
          {
            RAST._IExpr _2193_lo;
            DCOMP._IOwnership _2194___v221;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2195_recIdentsLo;
            RAST._IExpr _out635;
            DCOMP._IOwnership _out636;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out637;
            (this).GenExpr(_2190_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out635, out _out636, out _out637);
            _2193_lo = _out635;
            _2194___v221 = _out636;
            _2195_recIdentsLo = _out637;
            RAST._IExpr _2196_hi;
            DCOMP._IOwnership _2197___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2198_recIdentsHi;
            RAST._IExpr _out638;
            DCOMP._IOwnership _out639;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out640;
            (this).GenExpr(_2191_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out638, out _out639, out _out640);
            _2196_hi = _out638;
            _2197___v222 = _out639;
            _2198_recIdentsHi = _out640;
            if (_2192_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2193_lo, _2196_hi));
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2196_hi, _2193_lo));
            }
            RAST._IExpr _out641;
            DCOMP._IOwnership _out642;
            (this).FromOwned(r, expectedOwnership, out _out641, out _out642);
            r = _out641;
            resultingOwnership = _out642;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2195_recIdentsLo, _2198_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_UnboundedIntRange) {
          DAST._IExpression _2199_start = _source95.dtor_start;
          bool _2200_up = _source95.dtor_up;
          unmatched95 = false;
          {
            RAST._IExpr _2201_start;
            DCOMP._IOwnership _2202___v223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2203_recIdentStart;
            RAST._IExpr _out643;
            DCOMP._IOwnership _out644;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out645;
            (this).GenExpr(_2199_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out643, out _out644, out _out645);
            _2201_start = _out643;
            _2202___v223 = _out644;
            _2203_recIdentStart = _out645;
            if (_2200_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).Apply1(_2201_start);
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).Apply1(_2201_start);
            }
            RAST._IExpr _out646;
            DCOMP._IOwnership _out647;
            (this).FromOwned(r, expectedOwnership, out _out646, out _out647);
            r = _out646;
            resultingOwnership = _out647;
            readIdents = _2203_recIdentStart;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_MapBuilder) {
          DAST._IType _2204_keyType = _source95.dtor_keyType;
          DAST._IType _2205_valueType = _source95.dtor_valueType;
          unmatched95 = false;
          {
            RAST._IType _2206_kType;
            RAST._IType _out648;
            _out648 = (this).GenType(_2204_keyType, DCOMP.GenTypeContext.@default());
            _2206_kType = _out648;
            RAST._IType _2207_vType;
            RAST._IType _out649;
            _out649 = (this).GenType(_2205_valueType, DCOMP.GenTypeContext.@default());
            _2207_vType = _out649;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2206_kType, _2207_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out650;
            DCOMP._IOwnership _out651;
            (this).FromOwned(r, expectedOwnership, out _out650, out _out651);
            r = _out650;
            resultingOwnership = _out651;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_SetBuilder) {
          DAST._IType _2208_elemType = _source95.dtor_elemType;
          unmatched95 = false;
          {
            RAST._IType _2209_eType;
            RAST._IType _out652;
            _out652 = (this).GenType(_2208_elemType, DCOMP.GenTypeContext.@default());
            _2209_eType = _out652;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2209_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out653;
            DCOMP._IOwnership _out654;
            (this).FromOwned(r, expectedOwnership, out _out653, out _out654);
            r = _out653;
            resultingOwnership = _out654;
            return ;
          }
        }
      }
      if (unmatched95) {
        DAST._IType _2210_elemType = _source95.dtor_elemType;
        DAST._IExpression _2211_collection = _source95.dtor_collection;
        bool _2212_is__forall = _source95.dtor_is__forall;
        DAST._IExpression _2213_lambda = _source95.dtor_lambda;
        unmatched95 = false;
        {
          RAST._IType _2214_tpe;
          RAST._IType _out655;
          _out655 = (this).GenType(_2210_elemType, DCOMP.GenTypeContext.@default());
          _2214_tpe = _out655;
          RAST._IExpr _2215_collectionGen;
          DCOMP._IOwnership _2216___v224;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2217_recIdents;
          RAST._IExpr _out656;
          DCOMP._IOwnership _out657;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out658;
          (this).GenExpr(_2211_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out656, out _out657, out _out658);
          _2215_collectionGen = _out656;
          _2216___v224 = _out657;
          _2217_recIdents = _out658;
          Dafny.ISequence<DAST._IAttribute> _2218_extraAttributes;
          _2218_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2211_collection).is_IntRange) || ((_2211_collection).is_UnboundedIntRange)) || ((_2211_collection).is_SeqBoundedPool)) {
            _2218_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2213_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2219_formals;
            _2219_formals = (_2213_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2220_newFormals;
            _2220_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi50 = new BigInteger((_2219_formals).Count);
            for (BigInteger _2221_i = BigInteger.Zero; _2221_i < _hi50; _2221_i++) {
              var _pat_let_tv143 = _2218_extraAttributes;
              var _pat_let_tv144 = _2219_formals;
              _2220_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2220_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2219_formals).Select(_2221_i), _pat_let38_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let38_0, _2222_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv143, ((_pat_let_tv144).Select(_2221_i)).dtor_attributes), _pat_let39_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let39_0, _2223_dt__update_hattributes_h0 => DAST.Formal.create((_2222_dt__update__tmp_h0).dtor_name, (_2222_dt__update__tmp_h0).dtor_typ, _2223_dt__update_hattributes_h0)))))));
            }
            var _pat_let_tv145 = _2220_newFormals;
            DAST._IExpression _2224_newLambda;
            _2224_newLambda = Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_2213_lambda, _pat_let40_0 => Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_pat_let40_0, _2225_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let_tv145, _pat_let41_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let41_0, _2226_dt__update_hparams_h0 => DAST.Expression.create_Lambda(_2226_dt__update_hparams_h0, (_2225_dt__update__tmp_h1).dtor_retType, (_2225_dt__update__tmp_h1).dtor_body)))));
            RAST._IExpr _2227_lambdaGen;
            DCOMP._IOwnership _2228___v225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2229_recLambdaIdents;
            RAST._IExpr _out659;
            DCOMP._IOwnership _out660;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out661;
            (this).GenExpr(_2224_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out659, out _out660, out _out661);
            _2227_lambdaGen = _out659;
            _2228___v225 = _out660;
            _2229_recLambdaIdents = _out661;
            Dafny.ISequence<Dafny.Rune> _2230_fn;
            _2230_fn = ((_2212_is__forall) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any")));
            r = ((_2215_collectionGen).Sel(_2230_fn)).Apply1(((_2227_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2217_recIdents, _2229_recLambdaIdents);
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Quantifier without an inline lambda"));
            r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
          RAST._IExpr _out662;
          DCOMP._IOwnership _out663;
          (this).FromOwned(r, expectedOwnership, out _out662, out _out663);
          r = _out662;
          resultingOwnership = _out663;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      BigInteger _2231_i;
      _2231_i = BigInteger.Zero;
      while ((_2231_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _2232_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _2233_m;
        RAST._IMod _out664;
        _out664 = (this).GenModule((p).Select(_2231_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2233_m = _out664;
        _2232_generated = (_2233_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_2231_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2232_generated);
        _2231_i = (_2231_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2234_i;
      _2234_i = BigInteger.Zero;
      while ((_2234_i) < (new BigInteger((fullName).Count))) {
        if ((_2234_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2234_i)));
        _2234_i = (_2234_i) + (BigInteger.One);
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