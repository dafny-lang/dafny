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
      if ((new BigInteger((rs).Count)).Sign == 0) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      } else {
        Std.Wrappers._IOption<DAST._IResolvedType> _1121_res = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
          DAST._IType _source51 = (rs).Select(BigInteger.Zero);
          {
            if (_source51.is_UserDefined) {
              DAST._IResolvedType _1122_resolvedType = _source51.dtor_resolved;
              return DCOMP.__default.TraitTypeContainingMethod(_1122_resolvedType, dafnyName);
            }
          }
          {
            return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
          }
        }))();
        Std.Wrappers._IOption<DAST._IResolvedType> _source52 = _1121_res;
        {
          if (_source52.is_Some) {
            return _1121_res;
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
        {
          if (_source53.is_Module) {
            DAST._IModule _1137_m = _source53.dtor_Module_a0;
            RAST._IMod _1138_mm;
            RAST._IMod _out16;
            _out16 = (this).GenModule(_1137_m, containingPath);
            _1138_mm = _out16;
            _1136_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1138_mm));
            goto after_match1;
          }
        }
        {
          if (_source53.is_Class) {
            DAST._IClass _1139_c = _source53.dtor_Class_a0;
            Dafny.ISequence<RAST._IModDecl> _out17;
            _out17 = (this).GenClass(_1139_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1139_c).dtor_name)));
            _1136_generated = _out17;
            goto after_match1;
          }
        }
        {
          if (_source53.is_Trait) {
            DAST._ITrait _1140_t = _source53.dtor_Trait_a0;
            Dafny.ISequence<RAST._IModDecl> _out18;
            _out18 = (this).GenTrait(_1140_t, containingPath);
            _1136_generated = _out18;
            goto after_match1;
          }
        }
        {
          if (_source53.is_Newtype) {
            DAST._INewtype _1141_n = _source53.dtor_Newtype_a0;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenNewtype(_1141_n);
            _1136_generated = _out19;
            goto after_match1;
          }
        }
        {
          if (_source53.is_SynonymType) {
            DAST._ISynonymType _1142_s = _source53.dtor_SynonymType_a0;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenSynonymType(_1142_s);
            _1136_generated = _out20;
            goto after_match1;
          }
        }
        {
          DAST._IDatatype _1143_d = _source53.dtor_Datatype_a0;
          Dafny.ISequence<RAST._IModDecl> _out21;
          _out21 = (this).GenDatatype(_1143_d);
          _1136_generated = _out21;
        }
      after_match1: ;
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
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) {
        _1144_genTpConstraint = Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq);
      } else {
        _1144_genTpConstraint = Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType);
      }
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
        {
          if (_source54.is_Some) {
            DAST._IExpression _1161_e = _source54.dtor_value;
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
            goto after_match2;
          }
        }
        {
          {
            RAST._IExpr _1165_default;
            _1165_default = RAST.__default.std__Default__default;
            if ((_1159_fieldType).IsObjectOrPointer()) {
              _1165_default = (_1159_fieldType).ToNullExpr();
            }
            _1156_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1156_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1160_fieldRustName, _1165_default)));
          }
        }
      after_match2: ;
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
        {
          if (_source55.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source55.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1179_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _1180_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
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
              goto after_match3;
            }
          }
        }
        {
        }
      after_match3: ;
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
      {
        if (_source56.is_Some) {
          RAST._IType _1206_v = _source56.dtor_value;
          _1205_underlyingType = _1206_v;
          goto after_match4;
        }
      }
      {
        RAST._IType _out51;
        _out51 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
        _1205_underlyingType = _out51;
      }
    after_match4: ;
      DAST._IType _1207_resultingType;
      _1207_resultingType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _1208_newtypeName;
      _1208_newtypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1208_newtypeName, _1202_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1205_underlyingType))))));
      RAST._IExpr _1209_fnBody;
      _1209_fnBody = RAST.Expr.create_Identifier(_1208_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source57 = (c).dtor_witnessExpr;
      {
        if (_source57.is_Some) {
          DAST._IExpression _1210_e = _source57.dtor_value;
          {
            DAST._IExpression _1211_e;
            if (object.Equals((c).dtor_base, _1207_resultingType)) {
              _1211_e = _1210_e;
            } else {
              _1211_e = DAST.Expression.create_Convert(_1210_e, (c).dtor_base, _1207_resultingType);
            }
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
          goto after_match5;
        }
      }
      {
        {
          _1209_fnBody = (_1209_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
    after_match5: ;
      RAST._IImplMember _1215_body;
      _1215_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1209_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source58 = (c).dtor_constraint;
      {
        if (_source58.is_None) {
          goto after_match6;
        }
      }
      {
        DAST._INewtypeConstraint value8 = _source58.dtor_value;
        DAST._IFormal _1216_formal = value8.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _1217_constraintStmts = value8.dtor_constraintStmts;
        RAST._IExpr _1218_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1219___v57;
        DCOMP._IEnvironment _1220_newEnv;
        RAST._IExpr _out55;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out56;
        DCOMP._IEnvironment _out57;
        (this).GenStmts(_1217_constraintStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out55, out _out56, out _out57);
        _1218_rStmts = _out55;
        _1219___v57 = _out56;
        _1220_newEnv = _out57;
        Dafny.ISequence<RAST._IFormal> _1221_rFormals;
        Dafny.ISequence<RAST._IFormal> _out58;
        _out58 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_1216_formal));
        _1221_rFormals = _out58;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1202_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1208_newtypeName), _1201_rTypeParams), _1203_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _1221_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1218_rStmts))))))));
      }
    after_match6: ;
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
      {
        if (_source59.is_Some) {
          DAST._IExpression _1229_e = _source59.dtor_value;
          {
            RAST._IExpr _1230_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1231___v58;
            DCOMP._IEnvironment _1232_newEnv;
            RAST._IExpr _out64;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out65;
            DCOMP._IEnvironment _out66;
            (this).GenStmts((c).dtor_witnessStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out64, out _out65, out _out66);
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
          goto after_match7;
        }
      }
      {
      }
    after_match7: ;
      return s;
    }
    public bool TypeIsEq(DAST._IType t) {
      DAST._IType _source60 = t;
      {
        if (_source60.is_UserDefined) {
          return true;
        }
      }
      {
        if (_source60.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1237_ts = _source60.dtor_Tuple_a0;
          return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, bool>>((_1238_ts) => Dafny.Helpers.Quantifier<DAST._IType>((_1238_ts).UniqueElements, true, (((_forall_var_5) => {
            DAST._IType _1239_t = (DAST._IType)_forall_var_5;
            return !((_1238_ts).Contains(_1239_t)) || ((this).TypeIsEq(_1239_t));
          }))))(_1237_ts);
        }
      }
      {
        if (_source60.is_Array) {
          DAST._IType _1240_t = _source60.dtor_element;
          return (this).TypeIsEq(_1240_t);
        }
      }
      {
        if (_source60.is_Seq) {
          DAST._IType _1241_t = _source60.dtor_element;
          return (this).TypeIsEq(_1241_t);
        }
      }
      {
        if (_source60.is_Set) {
          DAST._IType _1242_t = _source60.dtor_element;
          return (this).TypeIsEq(_1242_t);
        }
      }
      {
        if (_source60.is_Multiset) {
          DAST._IType _1243_t = _source60.dtor_element;
          return (this).TypeIsEq(_1243_t);
        }
      }
      {
        if (_source60.is_Map) {
          DAST._IType _1244_k = _source60.dtor_key;
          DAST._IType _1245_v = _source60.dtor_value;
          return ((this).TypeIsEq(_1244_k)) && ((this).TypeIsEq(_1245_v));
        }
      }
      {
        if (_source60.is_SetBuilder) {
          DAST._IType _1246_t = _source60.dtor_element;
          return (this).TypeIsEq(_1246_t);
        }
      }
      {
        if (_source60.is_MapBuilder) {
          DAST._IType _1247_k = _source60.dtor_key;
          DAST._IType _1248_v = _source60.dtor_value;
          return ((this).TypeIsEq(_1247_k)) && ((this).TypeIsEq(_1248_v));
        }
      }
      {
        if (_source60.is_Arrow) {
          return false;
        }
      }
      {
        if (_source60.is_Primitive) {
          return true;
        }
      }
      {
        if (_source60.is_Passthrough) {
          return true;
        }
      }
      {
        if (_source60.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _1249_i = _source60.dtor_TypeArg_a0;
          return true;
        }
      }
      {
        return true;
      }
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
      Dafny.ISequence<RAST._IExpr> _1261_singletonConstructors;
      _1261_singletonConstructors = Dafny.Sequence<RAST._IExpr>.FromElements();
      BigInteger _hi12 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1262_i = BigInteger.Zero; _1262_i < _hi12; _1262_i++) {
        DAST._IDatatypeCtor _1263_ctor;
        _1263_ctor = ((c).dtor_ctors).Select(_1262_i);
        Dafny.ISequence<RAST._IField> _1264_ctorArgs;
        _1264_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1265_isNumeric;
        _1265_isNumeric = false;
        if ((new BigInteger(((_1263_ctor).dtor_args).Count)).Sign == 0) {
          RAST._IExpr _1266_instantiation;
          _1266_instantiation = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_1257_datatypeName)).MSel(DCOMP.__default.escapeName((_1263_ctor).dtor_name)), Dafny.Sequence<RAST._IAssignIdentifier>.FromElements());
          if ((this).IsRcWrapped((c).dtor_attributes)) {
            _1266_instantiation = RAST.__default.RcNew(_1266_instantiation);
          }
          _1261_singletonConstructors = Dafny.Sequence<RAST._IExpr>.Concat(_1261_singletonConstructors, Dafny.Sequence<RAST._IExpr>.FromElements(_1266_instantiation));
        }
        BigInteger _hi13 = new BigInteger(((_1263_ctor).dtor_args).Count);
        for (BigInteger _1267_j = BigInteger.Zero; _1267_j < _hi13; _1267_j++) {
          DAST._IDatatypeDtor _1268_dtor;
          _1268_dtor = ((_1263_ctor).dtor_args).Select(_1267_j);
          RAST._IType _1269_formalType;
          RAST._IType _out74;
          _out74 = (this).GenType(((_1268_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
          _1269_formalType = _out74;
          Dafny.ISequence<Dafny.Rune> _1270_formalName;
          _1270_formalName = DCOMP.__default.escapeName(((_1268_dtor).dtor_formal).dtor_name);
          if (((_1267_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1270_formalName))) {
            _1265_isNumeric = true;
          }
          if ((((_1267_j).Sign != 0) && (_1265_isNumeric)) && (!(Std.Strings.__default.OfNat(_1267_j)).Equals(_1270_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1270_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1267_j)));
            _1265_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1264_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1264_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1270_formalName, RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1269_formalType))))));
          } else {
            _1264_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1264_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1270_formalName, _1269_formalType))));
          }
        }
        RAST._IFields _1271_namedFields;
        _1271_namedFields = RAST.Fields.create_NamedFields(_1264_ctorArgs);
        if (_1265_isNumeric) {
          _1271_namedFields = (_1271_namedFields).ToNamelessFields();
        }
        _1258_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1258_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1263_ctor).dtor_name), _1271_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1272_selfPath;
      _1272_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1273_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1274_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out75;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out76;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1272_selfPath, _1253_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype(_1259_variances), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1253_typeParamsSeq, out _out75, out _out76);
      _1273_implBodyRaw = _out75;
      _1274_traitBodies = _out76;
      Dafny.ISequence<RAST._IImplMember> _1275_implBody;
      _1275_implBody = _1273_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1276_emittedFields;
      _1276_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi14 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1277_i = BigInteger.Zero; _1277_i < _hi14; _1277_i++) {
        DAST._IDatatypeCtor _1278_ctor;
        _1278_ctor = ((c).dtor_ctors).Select(_1277_i);
        BigInteger _hi15 = new BigInteger(((_1278_ctor).dtor_args).Count);
        for (BigInteger _1279_j = BigInteger.Zero; _1279_j < _hi15; _1279_j++) {
          DAST._IDatatypeDtor _1280_dtor;
          _1280_dtor = ((_1278_ctor).dtor_args).Select(_1279_j);
          Dafny.ISequence<Dafny.Rune> _1281_callName;
          _1281_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1280_dtor).dtor_callName, DCOMP.__default.escapeName(((_1280_dtor).dtor_formal).dtor_name));
          if (!((_1276_emittedFields).Contains(_1281_callName))) {
            _1276_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1276_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1281_callName));
            RAST._IType _1282_formalType;
            RAST._IType _out77;
            _out77 = (this).GenType(((_1280_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
            _1282_formalType = _out77;
            Dafny.ISequence<RAST._IMatchCase> _1283_cases;
            _1283_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1284_k = BigInteger.Zero; _1284_k < _hi16; _1284_k++) {
              DAST._IDatatypeCtor _1285_ctor2;
              _1285_ctor2 = ((c).dtor_ctors).Select(_1284_k);
              Dafny.ISequence<Dafny.Rune> _1286_pattern;
              _1286_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1257_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1285_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1287_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1288_hasMatchingField;
              _1288_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1289_patternInner;
              _1289_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1290_isNumeric;
              _1290_isNumeric = false;
              BigInteger _hi17 = new BigInteger(((_1285_ctor2).dtor_args).Count);
              for (BigInteger _1291_l = BigInteger.Zero; _1291_l < _hi17; _1291_l++) {
                DAST._IDatatypeDtor _1292_dtor2;
                _1292_dtor2 = ((_1285_ctor2).dtor_args).Select(_1291_l);
                Dafny.ISequence<Dafny.Rune> _1293_patternName;
                _1293_patternName = DCOMP.__default.escapeDtor(((_1292_dtor2).dtor_formal).dtor_name);
                Dafny.ISequence<Dafny.Rune> _1294_varName;
                _1294_varName = DCOMP.__default.escapeField(((_1292_dtor2).dtor_formal).dtor_name);
                if (((_1291_l).Sign == 0) && ((_1293_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1290_isNumeric = true;
                }
                if (_1290_isNumeric) {
                  _1293_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1292_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1291_l)));
                  _1294_varName = _1293_patternName;
                }
                if (object.Equals(((_1280_dtor).dtor_formal).dtor_name, ((_1292_dtor2).dtor_formal).dtor_name)) {
                  _1288_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1294_varName);
                }
                _1289_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1289_patternInner, _1293_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1290_isNumeric) {
                _1286_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1286_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1289_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1286_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1286_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1289_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1288_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1287_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1288_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1287_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1288_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1287_rhs = (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("field does not exist on this variant"));
              }
              RAST._IMatchCase _1295_ctorMatch;
              _1295_ctorMatch = RAST.MatchCase.create(_1286_pattern, RAST.Expr.create_RawExpr(_1287_rhs));
              _1283_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1283_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1295_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1283_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1283_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1257_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr((this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))))));
            }
            RAST._IExpr _1296_methodBody;
            _1296_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1283_cases);
            _1275_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1275_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1281_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1282_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1296_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _1297_coerceTypes;
      _1297_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1298_rCoerceTypeParams;
      _1298_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _1299_coerceArguments;
      _1299_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _1300_coerceMap;
      _1300_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _1301_rCoerceMap;
      _1301_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1302_coerceMapToArg;
      _1302_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1303_types;
        _1303_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi18 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1304_typeI = BigInteger.Zero; _1304_typeI < _hi18; _1304_typeI++) {
          DAST._ITypeArgDecl _1305_typeParam;
          _1305_typeParam = ((c).dtor_typeParams).Select(_1304_typeI);
          DAST._IType _1306_typeArg;
          RAST._ITypeParamDecl _1307_rTypeParamDecl;
          DAST._IType _out78;
          RAST._ITypeParamDecl _out79;
          (this).GenTypeParam(_1305_typeParam, out _out78, out _out79);
          _1306_typeArg = _out78;
          _1307_rTypeParamDecl = _out79;
          RAST._IType _1308_rTypeArg;
          RAST._IType _out80;
          _out80 = (this).GenType(_1306_typeArg, DCOMP.GenTypeContext.@default());
          _1308_rTypeArg = _out80;
          _1303_types = Dafny.Sequence<RAST._IType>.Concat(_1303_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1308_rTypeArg))));
          if (((_1304_typeI) < (new BigInteger((_1259_variances).Count))) && (((_1259_variances).Select(_1304_typeI)).is_Nonvariant)) {
            _1297_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1297_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1308_rTypeArg));
            goto continue0;
          }
          DAST._ITypeArgDecl _1309_coerceTypeParam;
          DAST._ITypeArgDecl _1310_dt__update__tmp_h0 = _1305_typeParam;
          Dafny.ISequence<Dafny.Rune> _1311_dt__update_hname_h0 = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_1304_typeI));
          _1309_coerceTypeParam = DAST.TypeArgDecl.create(_1311_dt__update_hname_h0, (_1310_dt__update__tmp_h0).dtor_bounds, (_1310_dt__update__tmp_h0).dtor_variance);
          DAST._IType _1312_coerceTypeArg;
          RAST._ITypeParamDecl _1313_rCoerceTypeParamDecl;
          DAST._IType _out81;
          RAST._ITypeParamDecl _out82;
          (this).GenTypeParam(_1309_coerceTypeParam, out _out81, out _out82);
          _1312_coerceTypeArg = _out81;
          _1313_rCoerceTypeParamDecl = _out82;
          _1300_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_1300_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_1306_typeArg, _1312_coerceTypeArg)));
          RAST._IType _1314_rCoerceType;
          RAST._IType _out83;
          _out83 = (this).GenType(_1312_coerceTypeArg, DCOMP.GenTypeContext.@default());
          _1314_rCoerceType = _out83;
          _1301_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_1301_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_1308_rTypeArg, _1314_rCoerceType)));
          _1297_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1297_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1314_rCoerceType));
          _1298_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1298_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1313_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _1315_coerceFormal;
          _1315_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_1304_typeI));
          _1302_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_1302_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_1308_rTypeArg, _1314_rCoerceType), (RAST.Expr.create_Identifier(_1315_coerceFormal)).Clone())));
          _1299_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_1299_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1315_coerceFormal, RAST.__default.Rc(RAST.Type.create_IntersectionType(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_1308_rTypeArg), _1314_rCoerceType)), RAST.__default.StaticTrait)))));
        continue0: ;
        }
      after0: ;
        _1258_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1258_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1316_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1316_tpe);
})), _1303_types)))));
      }
      bool _1317_cIsEq;
      _1317_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_1317_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _1257_datatypeName, _1255_rTypeParamsDecls, _1258_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1255_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams), _1256_whereConstraints, _1275_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1318_printImplBodyCases;
      _1318_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1319_hashImplBodyCases;
      _1319_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1320_coerceImplBodyCases;
      _1320_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi19 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1321_i = BigInteger.Zero; _1321_i < _hi19; _1321_i++) {
        DAST._IDatatypeCtor _1322_ctor;
        _1322_ctor = ((c).dtor_ctors).Select(_1321_i);
        Dafny.ISequence<Dafny.Rune> _1323_ctorMatch;
        _1323_ctorMatch = DCOMP.__default.escapeName((_1322_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1324_modulePrefix;
        if (((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) {
          _1324_modulePrefix = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        } else {
          _1324_modulePrefix = Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."));
        }
        Dafny.ISequence<Dafny.Rune> _1325_ctorName;
        _1325_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1324_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1322_ctor).dtor_name));
        if (((new BigInteger((_1325_ctorName).Count)) >= (new BigInteger(13))) && (((_1325_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1325_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1326_printRhs;
        _1326_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1325_ctorName), (((_1322_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1327_hashRhs;
        _1327_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        Dafny.ISequence<RAST._IAssignIdentifier> _1328_coerceRhsArgs;
        _1328_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _1329_isNumeric;
        _1329_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1330_ctorMatchInner;
        _1330_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi20 = new BigInteger(((_1322_ctor).dtor_args).Count);
        for (BigInteger _1331_j = BigInteger.Zero; _1331_j < _hi20; _1331_j++) {
          DAST._IDatatypeDtor _1332_dtor;
          _1332_dtor = ((_1322_ctor).dtor_args).Select(_1331_j);
          Dafny.ISequence<Dafny.Rune> _1333_patternName;
          _1333_patternName = DCOMP.__default.escapeDtor(((_1332_dtor).dtor_formal).dtor_name);
          Dafny.ISequence<Dafny.Rune> _1334_fieldName;
          _1334_fieldName = DCOMP.__default.escapeField(((_1332_dtor).dtor_formal).dtor_name);
          DAST._IType _1335_formalType;
          _1335_formalType = ((_1332_dtor).dtor_formal).dtor_typ;
          if (((_1331_j).Sign == 0) && ((_1334_fieldName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1329_isNumeric = true;
          }
          if (_1329_isNumeric) {
            _1334_fieldName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1332_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1331_j)));
          }
          if ((_1335_formalType).is_Arrow) {
            _1327_hashRhs = (_1327_hashRhs).Then(((RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))));
          } else {
            _1327_hashRhs = (_1327_hashRhs).Then(((RAST.Expr.create_Identifier(_1334_fieldName)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))));
          }
          _1330_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1330_ctorMatchInner, ((_1329_isNumeric) ? (_1334_fieldName) : (_1333_patternName))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1331_j).Sign == 1) {
            _1326_printRhs = (_1326_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1326_printRhs = (_1326_printRhs).Then(RAST.Expr.create_RawExpr((((_1335_formalType).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \"<function>\")?")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1334_fieldName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))))));
          RAST._IExpr _1336_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _1337_formalTpe;
          RAST._IType _out84;
          _out84 = (this).GenType(_1335_formalType, DCOMP.GenTypeContext.@default());
          _1337_formalTpe = _out84;
          DAST._IType _1338_newFormalType;
          _1338_newFormalType = (_1335_formalType).Replace(_1300_coerceMap);
          RAST._IType _1339_newFormalTpe;
          _1339_newFormalTpe = (_1337_formalTpe).Replace(_1301_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1340_upcastConverter;
          _1340_upcastConverter = (this).UpcastConversionLambda(_1335_formalType, _1337_formalTpe, _1338_newFormalType, _1339_newFormalTpe, _1302_coerceMapToArg);
          if ((_1340_upcastConverter).is_Success) {
            RAST._IExpr _1341_coercionFunction;
            _1341_coercionFunction = (_1340_upcastConverter).dtor_value;
            _1336_coerceRhsArg = (_1341_coercionFunction).Apply1(RAST.Expr.create_Identifier(_1333_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_1331_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _1257_datatypeName));
            _1336_coerceRhsArg = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("todo!"))).Apply1(RAST.Expr.create_LiteralString((this.error).dtor_value, false, false));
          }
          _1328_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1328_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1333_patternName, _1336_coerceRhsArg)));
        }
        RAST._IExpr _1342_coerceRhs;
        _1342_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_1257_datatypeName)).MSel(DCOMP.__default.escapeName((_1322_ctor).dtor_name)), _1328_coerceRhsArgs);
        if (_1329_isNumeric) {
          _1323_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1323_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1330_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1323_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1323_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1330_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1322_ctor).dtor_hasAnyArgs) {
          _1326_printRhs = (_1326_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1326_printRhs = (_1326_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1318_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1318_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1257_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1323_ctorMatch), RAST.Expr.create_Block(_1326_printRhs))));
        _1319_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1319_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1257_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1323_ctorMatch), RAST.Expr.create_Block(_1327_hashRhs))));
        _1320_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1320_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1257_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1323_ctorMatch), RAST.Expr.create_Block(_1342_coerceRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IMatchCase> _1343_extraCases;
        _1343_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1257_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{"), (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}")))));
        _1318_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1318_printImplBodyCases, _1343_extraCases);
        _1319_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1319_hashImplBodyCases, _1343_extraCases);
        _1320_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1320_coerceImplBodyCases, _1343_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1344_defaultConstrainedTypeParams;
      _1344_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1255_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1345_rTypeParamsDeclsWithEq;
      _1345_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1255_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1346_rTypeParamsDeclsWithHash;
      _1346_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1255_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1347_printImplBody;
      _1347_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1318_printImplBodyCases);
      RAST._IExpr _1348_hashImplBody;
      _1348_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1319_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1255_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1255_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1347_printImplBody))))))));
      if ((new BigInteger((_1298_rCoerceTypeParams).Count)).Sign == 1) {
        RAST._IExpr _1349_coerceImplBody;
        _1349_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _1320_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1255_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), _1298_rCoerceTypeParams, _1299_coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams)), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1297_coerceTypes))))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.RcNew(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.Type.create_SelfOwned())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1297_coerceTypes)), _1349_coerceImplBody))))))))));
      }
      if ((new BigInteger((_1261_singletonConstructors).Count)) == (new BigInteger(((c).dtor_ctors).Count))) {
        RAST._IType _1350_datatypeType;
        _1350_datatypeType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams);
        RAST._IType _1351_instantiationType;
        if ((this).IsRcWrapped((c).dtor_attributes)) {
          _1351_instantiationType = RAST.__default.Rc(_1350_datatypeType);
        } else {
          _1351_instantiationType = _1350_datatypeType;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1255_rTypeParamsDecls, _1350_datatypeType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_AllSingletonConstructors"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SequenceIter"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1351_instantiationType))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_1261_singletonConstructors)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())))))))));
      }
      if (_1317_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1345_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1346_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1348_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1352_structName;
        _1352_structName = (RAST.Expr.create_Identifier(_1257_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1353_structAssignments;
        _1353_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi21 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1354_i = BigInteger.Zero; _1354_i < _hi21; _1354_i++) {
          DAST._IDatatypeDtor _1355_dtor;
          _1355_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1354_i);
          _1353_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1353_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1355_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1356_defaultConstrainedTypeParams;
        _1356_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1255_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1357_fullType;
        _1357_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams);
        if (_1317_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1356_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1357_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1357_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1352_structName, _1353_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1255_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_1357_fullType), RAST.Type.create_Borrowed(_1357_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
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
        if (((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))) {
          r = RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        } else if (((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"))) {
          r = RAST.__default.dafny__runtime__type;
        } else {
          r = RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"));
        }
        BigInteger _hi22 = new BigInteger((p).Count);
        for (BigInteger _1358_i = BigInteger.Zero; _1358_i < _hi22; _1358_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1358_i))));
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
        if (((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))) {
          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        } else if (((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"))) {
          r = RAST.__default.dafny__runtime;
        } else {
          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"));
        }
        BigInteger _hi23 = new BigInteger((p).Count);
        for (BigInteger _1359_i = BigInteger.Zero; _1359_i < _hi23; _1359_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1359_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, DCOMP._IGenTypeContext genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi24 = new BigInteger((args).Count);
      for (BigInteger _1360_i = BigInteger.Zero; _1360_i < _hi24; _1360_i++) {
        RAST._IType _1361_genTp;
        RAST._IType _out85;
        _out85 = (this).GenType((args).Select(_1360_i), genTypeContext);
        _1361_genTp = _out85;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1361_genTp));
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
      {
        if (_source61.is_UserDefined) {
          DAST._IResolvedType _1362_resolved = _source61.dtor_resolved;
          {
            RAST._IType _1363_t;
            RAST._IType _out86;
            _out86 = DCOMP.COMP.GenPath((_1362_resolved).dtor_path);
            _1363_t = _out86;
            Dafny.ISequence<RAST._IType> _1364_typeArgs;
            Dafny.ISequence<RAST._IType> _out87;
            _out87 = (this).GenTypeArgs((_1362_resolved).dtor_typeArgs, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let9_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let9_0, _1365_dt__update__tmp_h0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let10_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let10_0, _1366_dt__update_hforTraitParents_h0 => DCOMP.GenTypeContext.create((_1365_dt__update__tmp_h0).dtor_inBinding, (_1365_dt__update__tmp_h0).dtor_inFn, _1366_dt__update_hforTraitParents_h0))))));
            _1364_typeArgs = _out87;
            s = RAST.Type.create_TypeApp(_1363_t, _1364_typeArgs);
            DAST._IResolvedTypeBase _source62 = (_1362_resolved).dtor_kind;
            {
              if (_source62.is_Class) {
                {
                  s = (this).Object(s);
                }
                goto after_match9;
              }
            }
            {
              if (_source62.is_Datatype) {
                {
                  if ((this).IsRcWrapped((_1362_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
                goto after_match9;
              }
            }
            {
              if (_source62.is_Trait) {
                {
                  if (((_1362_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
                  }
                  if (!((genTypeContext).dtor_forTraitParents)) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
                goto after_match9;
              }
            }
            {
              DAST._IType _1367_t = _source62.dtor_baseType;
              DAST._INewtypeRange _1368_range = _source62.dtor_range;
              bool _1369_erased = _source62.dtor_erase;
              {
                if (_1369_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source63 = DCOMP.COMP.NewtypeToRustType(_1367_t, _1368_range);
                  {
                    if (_source63.is_Some) {
                      RAST._IType _1370_v = _source63.dtor_value;
                      s = _1370_v;
                      goto after_match10;
                    }
                  }
                  {
                  }
                after_match10: ;
                }
              }
            }
          after_match9: ;
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_Object) {
          {
            s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
            if (!((genTypeContext).dtor_forTraitParents)) {
              s = (this).Object(RAST.Type.create_DynType(s));
            }
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1371_types = _source61.dtor_Tuple_a0;
          {
            Dafny.ISequence<RAST._IType> _1372_args;
            _1372_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1373_i;
            _1373_i = BigInteger.Zero;
            while ((_1373_i) < (new BigInteger((_1371_types).Count))) {
              RAST._IType _1374_generated;
              RAST._IType _out88;
              _out88 = (this).GenType((_1371_types).Select(_1373_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let11_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let11_0, _1375_dt__update__tmp_h1 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let12_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let12_0, _1376_dt__update_hforTraitParents_h1 => DCOMP.GenTypeContext.create((_1375_dt__update__tmp_h1).dtor_inBinding, (_1375_dt__update__tmp_h1).dtor_inFn, _1376_dt__update_hforTraitParents_h1))))));
              _1374_generated = _out88;
              _1372_args = Dafny.Sequence<RAST._IType>.Concat(_1372_args, Dafny.Sequence<RAST._IType>.FromElements(_1374_generated));
              _1373_i = (_1373_i) + (BigInteger.One);
            }
            if ((new BigInteger((_1371_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) {
              s = RAST.Type.create_TupleType(_1372_args);
            } else {
              s = RAST.__default.SystemTupleType(_1372_args);
            }
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_Array) {
          DAST._IType _1377_element = _source61.dtor_element;
          BigInteger _1378_dims = _source61.dtor_dims;
          {
            if ((_1378_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1379_elem;
              RAST._IType _out89;
              _out89 = (this).GenType(_1377_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let13_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let13_0, _1380_dt__update__tmp_h2 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let14_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let14_0, _1381_dt__update_hforTraitParents_h2 => DCOMP.GenTypeContext.create((_1380_dt__update__tmp_h2).dtor_inBinding, (_1380_dt__update__tmp_h2).dtor_inFn, _1381_dt__update_hforTraitParents_h2))))));
              _1379_elem = _out89;
              if ((_1378_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1379_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1382_n;
                _1382_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1378_dims));
                s = ((RAST.__default.dafny__runtime__type).MSel(_1382_n)).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1379_elem));
                s = (this).Object(s);
              }
            }
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_Seq) {
          DAST._IType _1383_element = _source61.dtor_element;
          {
            RAST._IType _1384_elem;
            RAST._IType _out90;
            _out90 = (this).GenType(_1383_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let15_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let15_0, _1385_dt__update__tmp_h3 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let16_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let16_0, _1386_dt__update_hforTraitParents_h3 => DCOMP.GenTypeContext.create((_1385_dt__update__tmp_h3).dtor_inBinding, (_1385_dt__update__tmp_h3).dtor_inFn, _1386_dt__update_hforTraitParents_h3))))));
            _1384_elem = _out90;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1384_elem));
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_Set) {
          DAST._IType _1387_element = _source61.dtor_element;
          {
            RAST._IType _1388_elem;
            RAST._IType _out91;
            _out91 = (this).GenType(_1387_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let17_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let17_0, _1389_dt__update__tmp_h4 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let18_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let18_0, _1390_dt__update_hforTraitParents_h4 => DCOMP.GenTypeContext.create((_1389_dt__update__tmp_h4).dtor_inBinding, (_1389_dt__update__tmp_h4).dtor_inFn, _1390_dt__update_hforTraitParents_h4))))));
            _1388_elem = _out91;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1388_elem));
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_Multiset) {
          DAST._IType _1391_element = _source61.dtor_element;
          {
            RAST._IType _1392_elem;
            RAST._IType _out92;
            _out92 = (this).GenType(_1391_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let19_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let19_0, _1393_dt__update__tmp_h5 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let20_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let20_0, _1394_dt__update_hforTraitParents_h5 => DCOMP.GenTypeContext.create((_1393_dt__update__tmp_h5).dtor_inBinding, (_1393_dt__update__tmp_h5).dtor_inFn, _1394_dt__update_hforTraitParents_h5))))));
            _1392_elem = _out92;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1392_elem));
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_Map) {
          DAST._IType _1395_key = _source61.dtor_key;
          DAST._IType _1396_value = _source61.dtor_value;
          {
            RAST._IType _1397_keyType;
            RAST._IType _out93;
            _out93 = (this).GenType(_1395_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let21_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let21_0, _1398_dt__update__tmp_h6 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let22_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let22_0, _1399_dt__update_hforTraitParents_h6 => DCOMP.GenTypeContext.create((_1398_dt__update__tmp_h6).dtor_inBinding, (_1398_dt__update__tmp_h6).dtor_inFn, _1399_dt__update_hforTraitParents_h6))))));
            _1397_keyType = _out93;
            RAST._IType _1400_valueType;
            RAST._IType _out94;
            _out94 = (this).GenType(_1396_value, genTypeContext);
            _1400_valueType = _out94;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1397_keyType, _1400_valueType));
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_MapBuilder) {
          DAST._IType _1401_key = _source61.dtor_key;
          DAST._IType _1402_value = _source61.dtor_value;
          {
            RAST._IType _1403_keyType;
            RAST._IType _out95;
            _out95 = (this).GenType(_1401_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let23_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let23_0, _1404_dt__update__tmp_h7 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let24_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let24_0, _1405_dt__update_hforTraitParents_h7 => DCOMP.GenTypeContext.create((_1404_dt__update__tmp_h7).dtor_inBinding, (_1404_dt__update__tmp_h7).dtor_inFn, _1405_dt__update_hforTraitParents_h7))))));
            _1403_keyType = _out95;
            RAST._IType _1406_valueType;
            RAST._IType _out96;
            _out96 = (this).GenType(_1402_value, genTypeContext);
            _1406_valueType = _out96;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1403_keyType, _1406_valueType));
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_SetBuilder) {
          DAST._IType _1407_elem = _source61.dtor_element;
          {
            RAST._IType _1408_elemType;
            RAST._IType _out97;
            _out97 = (this).GenType(_1407_elem, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let25_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let25_0, _1409_dt__update__tmp_h8 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let26_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let26_0, _1410_dt__update_hforTraitParents_h8 => DCOMP.GenTypeContext.create((_1409_dt__update__tmp_h8).dtor_inBinding, (_1409_dt__update__tmp_h8).dtor_inFn, _1410_dt__update_hforTraitParents_h8))))));
            _1408_elemType = _out97;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1408_elemType));
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1411_args = _source61.dtor_args;
          DAST._IType _1412_result = _source61.dtor_result;
          {
            Dafny.ISequence<RAST._IType> _1413_argTypes;
            _1413_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1414_i;
            _1414_i = BigInteger.Zero;
            while ((_1414_i) < (new BigInteger((_1411_args).Count))) {
              RAST._IType _1415_generated;
              RAST._IType _out98;
              _out98 = (this).GenType((_1411_args).Select(_1414_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let27_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let27_0, _1416_dt__update__tmp_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let28_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let28_0, _1417_dt__update_hforTraitParents_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(true, _pat_let29_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let29_0, _1418_dt__update_hinFn_h0 => DCOMP.GenTypeContext.create((_1416_dt__update__tmp_h9).dtor_inBinding, _1418_dt__update_hinFn_h0, _1417_dt__update_hforTraitParents_h9))))))));
              _1415_generated = _out98;
              _1413_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1413_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1415_generated)));
              _1414_i = (_1414_i) + (BigInteger.One);
            }
            RAST._IType _1419_resultType;
            RAST._IType _out99;
            _out99 = (this).GenType(_1412_result, DCOMP.GenTypeContext.create(((genTypeContext).dtor_inFn) || ((genTypeContext).dtor_inBinding), false, false));
            _1419_resultType = _out99;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1413_argTypes, _1419_resultType)));
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source61.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1420_name = _h90;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1420_name));
          goto after_match8;
        }
      }
      {
        if (_source61.is_Primitive) {
          DAST._IPrimitive _1421_p = _source61.dtor_Primitive_a0;
          {
            DAST._IPrimitive _source64 = _1421_p;
            {
              if (_source64.is_Int) {
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
                goto after_match11;
              }
            }
            {
              if (_source64.is_Real) {
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
                goto after_match11;
              }
            }
            {
              if (_source64.is_String) {
                s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
                goto after_match11;
              }
            }
            {
              if (_source64.is_Bool) {
                s = RAST.Type.create_Bool();
                goto after_match11;
              }
            }
            {
              s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
            }
          after_match11: ;
          }
          goto after_match8;
        }
      }
      {
        Dafny.ISequence<Dafny.Rune> _1422_v = _source61.dtor_Passthrough_a0;
        s = RAST.__default.RawType(_1422_v);
      }
    after_match8: ;
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
      for (BigInteger _1423_i = BigInteger.Zero; _1423_i < _hi25; _1423_i++) {
        DAST._IMethod _source65 = (body).Select(_1423_i);
        {
          DAST._IMethod _1424_m = _source65;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source66 = (_1424_m).dtor_overridingPath;
            {
              if (_source66.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1425_p = _source66.dtor_value;
                {
                  Dafny.ISequence<RAST._IImplMember> _1426_existing;
                  _1426_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1425_p)) {
                    _1426_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1425_p);
                  }
                  if (((new BigInteger(((_1424_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _1427_genMethod;
                  RAST._IImplMember _out100;
                  _out100 = (this).GenMethod(_1424_m, true, enclosingType, enclosingTypeParams);
                  _1427_genMethod = _out100;
                  _1426_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1426_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1427_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1425_p, _1426_existing)));
                }
                goto after_match13;
              }
            }
            {
              {
                RAST._IImplMember _1428_generated;
                RAST._IImplMember _out101;
                _out101 = (this).GenMethod(_1424_m, forTrait, enclosingType, enclosingTypeParams);
                _1428_generated = _out101;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1428_generated));
              }
            }
          after_match13: ;
          }
        }
      after_match12: ;
      }
    }
    public Dafny.ISequence<RAST._IFormal> GenParams(Dafny.ISequence<DAST._IFormal> @params)
    {
      Dafny.ISequence<RAST._IFormal> s = Dafny.Sequence<RAST._IFormal>.Empty;
      s = Dafny.Sequence<RAST._IFormal>.FromElements();
      BigInteger _hi26 = new BigInteger((@params).Count);
      for (BigInteger _1429_i = BigInteger.Zero; _1429_i < _hi26; _1429_i++) {
        DAST._IFormal _1430_param;
        _1430_param = (@params).Select(_1429_i);
        RAST._IType _1431_paramType;
        RAST._IType _out102;
        _out102 = (this).GenType((_1430_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _1431_paramType = _out102;
        if ((!((_1431_paramType).CanReadWithoutClone())) && (!((_1430_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1431_paramType = RAST.Type.create_Borrowed(_1431_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_1430_param).dtor_name), _1431_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1432_params;
      Dafny.ISequence<RAST._IFormal> _out103;
      _out103 = (this).GenParams((m).dtor_params);
      _1432_params = _out103;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1433_paramNames;
      _1433_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1434_paramTypes;
      _1434_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi27 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1435_paramI = BigInteger.Zero; _1435_paramI < _hi27; _1435_paramI++) {
        DAST._IFormal _1436_dafny__formal;
        _1436_dafny__formal = ((m).dtor_params).Select(_1435_paramI);
        RAST._IFormal _1437_formal;
        _1437_formal = (_1432_params).Select(_1435_paramI);
        Dafny.ISequence<Dafny.Rune> _1438_name;
        _1438_name = (_1437_formal).dtor_name;
        _1433_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1433_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1438_name));
        _1434_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1434_paramTypes, _1438_name, (_1437_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1439_fnName;
      _1439_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _1440_selfIdent;
      _1440_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1441_selfId;
        _1441_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((m).dtor_outVarsAreUninitFieldsToAssign) {
          _1441_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv2 = enclosingTypeParams;
        DAST._IType _1442_instanceType;
        DAST._IType _source67 = enclosingType;
        {
          if (_source67.is_UserDefined) {
            DAST._IResolvedType _1443_r = _source67.dtor_resolved;
            _1442_instanceType = DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_1443_r, _pat_let30_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let30_0, _1444_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv2, _pat_let31_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let31_0, _1445_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_1444_dt__update__tmp_h0).dtor_path, _1445_dt__update_htypeArgs_h0, (_1444_dt__update__tmp_h0).dtor_kind, (_1444_dt__update__tmp_h0).dtor_attributes, (_1444_dt__update__tmp_h0).dtor_properMethods, (_1444_dt__update__tmp_h0).dtor_extendedTypes))))));
            goto after_match14;
          }
        }
        {
          _1442_instanceType = enclosingType;
        }
      after_match14: ;
        if (forTrait) {
          RAST._IFormal _1446_selfFormal;
          if ((m).dtor_wasFunction) {
            _1446_selfFormal = RAST.Formal.selfBorrowed;
          } else {
            _1446_selfFormal = RAST.Formal.selfBorrowedMut;
          }
          _1432_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1446_selfFormal), _1432_params);
        } else {
          RAST._IType _1447_tpe;
          RAST._IType _out104;
          _out104 = (this).GenType(_1442_instanceType, DCOMP.GenTypeContext.@default());
          _1447_tpe = _out104;
          if ((_1441_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            _1447_tpe = RAST.Type.create_Borrowed(_1447_tpe);
          } else if ((_1441_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_1447_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _1447_tpe = RAST.__default.SelfBorrowed;
              } else {
                _1447_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              if ((((enclosingType).is_UserDefined) && ((((enclosingType).dtor_resolved).dtor_kind).is_Datatype)) && ((this).IsRcWrapped(((enclosingType).dtor_resolved).dtor_attributes))) {
                _1447_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.Type.create_SelfOwned()));
              } else {
                _1447_tpe = RAST.Type.create_Borrowed(RAST.Type.create_SelfOwned());
              }
            }
          }
          _1432_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1441_selfId, _1447_tpe)), _1432_params);
        }
        _1440_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_1441_selfId, _1442_instanceType);
      }
      Dafny.ISequence<RAST._IType> _1448_retTypeArgs;
      _1448_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1449_typeI;
      _1449_typeI = BigInteger.Zero;
      while ((_1449_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1450_typeExpr;
        RAST._IType _out105;
        _out105 = (this).GenType(((m).dtor_outTypes).Select(_1449_typeI), DCOMP.GenTypeContext.@default());
        _1450_typeExpr = _out105;
        _1448_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1448_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1450_typeExpr));
        _1449_typeI = (_1449_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1451_visibility;
      if (forTrait) {
        _1451_visibility = RAST.Visibility.create_PRIV();
      } else {
        _1451_visibility = RAST.Visibility.create_PUB();
      }
      Dafny.ISequence<DAST._ITypeArgDecl> _1452_typeParamsFiltered;
      _1452_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi28 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1453_typeParamI = BigInteger.Zero; _1453_typeParamI < _hi28; _1453_typeParamI++) {
        DAST._ITypeArgDecl _1454_typeParam;
        _1454_typeParam = ((m).dtor_typeParams).Select(_1453_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1454_typeParam).dtor_name)))) {
          _1452_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1452_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1454_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1455_typeParams;
      _1455_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1452_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi29 = new BigInteger((_1452_typeParamsFiltered).Count);
        for (BigInteger _1456_i = BigInteger.Zero; _1456_i < _hi29; _1456_i++) {
          DAST._IType _1457_typeArg;
          RAST._ITypeParamDecl _1458_rTypeParamDecl;
          DAST._IType _out106;
          RAST._ITypeParamDecl _out107;
          (this).GenTypeParam((_1452_typeParamsFiltered).Select(_1456_i), out _out106, out _out107);
          _1457_typeArg = _out106;
          _1458_rTypeParamDecl = _out107;
          RAST._ITypeParamDecl _1459_dt__update__tmp_h1 = _1458_rTypeParamDecl;
          Dafny.ISequence<RAST._IType> _1460_dt__update_hconstraints_h0 = Dafny.Sequence<RAST._IType>.Concat((_1458_rTypeParamDecl).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
          _1458_rTypeParamDecl = RAST.TypeParamDecl.create((_1459_dt__update__tmp_h1).dtor_content, _1460_dt__update_hconstraints_h0);
          _1455_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1455_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1458_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1461_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1462_env = DCOMP.Environment.Default();
      RAST._IExpr _1463_preBody;
      _1463_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1464_preAssignNames;
      _1464_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1465_preAssignTypes;
      _1465_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1466_earlyReturn;
        _1466_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None();
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source68 = (m).dtor_outVars;
        {
          if (_source68.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1467_outVars = _source68.dtor_value;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1466_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
                BigInteger _hi30 = new BigInteger((_1467_outVars).Count);
                for (BigInteger _1468_outI = BigInteger.Zero; _1468_outI < _hi30; _1468_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1469_outVar;
                  _1469_outVar = (_1467_outVars).Select(_1468_outI);
                  Dafny.ISequence<Dafny.Rune> _1470_outName;
                  _1470_outName = DCOMP.__default.escapeName((_1469_outVar));
                  Dafny.ISequence<Dafny.Rune> _1471_tracker__name;
                  _1471_tracker__name = DCOMP.__default.AddAssignedPrefix(_1470_outName);
                  _1464_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1464_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1471_tracker__name));
                  _1465_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1465_preAssignTypes, _1471_tracker__name, RAST.Type.create_Bool());
                  _1463_preBody = (_1463_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1471_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1472_tupleArgs;
                _1472_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
                BigInteger _hi31 = new BigInteger((_1467_outVars).Count);
                for (BigInteger _1473_outI = BigInteger.Zero; _1473_outI < _hi31; _1473_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1474_outVar;
                  _1474_outVar = (_1467_outVars).Select(_1473_outI);
                  RAST._IType _1475_outType;
                  RAST._IType _out108;
                  _out108 = (this).GenType(((m).dtor_outTypes).Select(_1473_outI), DCOMP.GenTypeContext.@default());
                  _1475_outType = _out108;
                  Dafny.ISequence<Dafny.Rune> _1476_outName;
                  _1476_outName = DCOMP.__default.escapeName((_1474_outVar));
                  _1433_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1433_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1476_outName));
                  RAST._IType _1477_outMaybeType;
                  if ((_1475_outType).CanReadWithoutClone()) {
                    _1477_outMaybeType = _1475_outType;
                  } else {
                    _1477_outMaybeType = RAST.__default.MaybePlaceboType(_1475_outType);
                  }
                  _1434_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1434_paramTypes, _1476_outName, _1477_outMaybeType);
                  _1472_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1472_tupleArgs, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1476_outName));
                }
                _1466_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(_1472_tupleArgs);
              }
            }
            goto after_match15;
          }
        }
        {
        }
      after_match15: ;
        _1462_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1464_preAssignNames, _1433_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1465_preAssignTypes, _1434_paramTypes));
        RAST._IExpr _1478_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1479___v69;
        DCOMP._IEnvironment _1480___v70;
        RAST._IExpr _out109;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out110;
        DCOMP._IEnvironment _out111;
        (this).GenStmts((m).dtor_body, _1440_selfIdent, _1462_env, true, _1466_earlyReturn, out _out109, out _out110, out _out111);
        _1478_body = _out109;
        _1479___v69 = _out110;
        _1480___v70 = _out111;
        _1461_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1463_preBody).Then(_1478_body));
      } else {
        _1462_env = DCOMP.Environment.create(_1433_paramNames, _1434_paramTypes);
        _1461_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1451_visibility, RAST.Fn.create(_1439_fnName, _1455_typeParams, _1432_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1448_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1448_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1448_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1461_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1481_declarations;
      _1481_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1482_i;
      _1482_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1483_stmts;
      _1483_stmts = stmts;
      while ((_1482_i) < (new BigInteger((_1483_stmts).Count))) {
        DAST._IStatement _1484_stmt;
        _1484_stmt = (_1483_stmts).Select(_1482_i);
        DAST._IStatement _source69 = _1484_stmt;
        {
          if (_source69.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1485_name = _source69.dtor_name;
            DAST._IType _1486_optType = _source69.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source69.dtor_maybeValue;
            if (maybeValue0.is_None) {
              if (((_1482_i) + (BigInteger.One)) < (new BigInteger((_1483_stmts).Count))) {
                DAST._IStatement _source70 = (_1483_stmts).Select((_1482_i) + (BigInteger.One));
                {
                  if (_source70.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source70.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> ident0 = lhs0.dtor_ident;
                      Dafny.ISequence<Dafny.Rune> _1487_name2 = ident0;
                      DAST._IExpression _1488_rhs = _source70.dtor_value;
                      if (object.Equals(_1487_name2, _1485_name)) {
                        _1483_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1483_stmts).Subsequence(BigInteger.Zero, _1482_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1485_name, _1486_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1488_rhs)))), (_1483_stmts).Drop((_1482_i) + (new BigInteger(2))));
                        _1484_stmt = (_1483_stmts).Select(_1482_i);
                      }
                      goto after_match17;
                    }
                  }
                }
                {
                }
              after_match17: ;
              }
              goto after_match16;
            }
          }
        }
        {
        }
      after_match16: ;
        RAST._IExpr _1489_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1490_recIdents;
        DCOMP._IEnvironment _1491_newEnv2;
        RAST._IExpr _out112;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out113;
        DCOMP._IEnvironment _out114;
        (this).GenStmt(_1484_stmt, selfIdent, newEnv, (isLast) && ((_1482_i) == ((new BigInteger((_1483_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out112, out _out113, out _out114);
        _1489_stmtExpr = _out112;
        _1490_recIdents = _out113;
        _1491_newEnv2 = _out114;
        newEnv = _1491_newEnv2;
        DAST._IStatement _source71 = _1484_stmt;
        {
          if (_source71.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1492_name = _source71.dtor_name;
            {
              _1481_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1481_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_1492_name)));
            }
            goto after_match18;
          }
        }
        {
        }
      after_match18: ;
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1490_recIdents, _1481_declarations));
        generated = (generated).Then(_1489_stmtExpr);
        _1482_i = (_1482_i) + (BigInteger.One);
        if ((_1489_stmtExpr).is_Return) {
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
      {
        if (_source72.is_Ident) {
          Dafny.ISequence<Dafny.Rune> ident1 = _source72.dtor_ident;
          Dafny.ISequence<Dafny.Rune> _1493_id = ident1;
          {
            Dafny.ISequence<Dafny.Rune> _1494_idRust;
            _1494_idRust = DCOMP.__default.escapeName(_1493_id);
            if (((env).IsBorrowed(_1494_idRust)) || ((env).IsBorrowedMut(_1494_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1494_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1494_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1494_idRust);
            needsIIFE = false;
          }
          goto after_match19;
        }
      }
      {
        if (_source72.is_Select) {
          DAST._IExpression _1495_on = _source72.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1496_field = _source72.dtor_field;
          {
            Dafny.ISequence<Dafny.Rune> _1497_fieldName;
            _1497_fieldName = DCOMP.__default.escapeName(_1496_field);
            RAST._IExpr _1498_onExpr;
            DCOMP._IOwnership _1499_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1500_recIdents;
            RAST._IExpr _out115;
            DCOMP._IOwnership _out116;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out117;
            (this).GenExpr(_1495_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out115, out _out116, out _out117);
            _1498_onExpr = _out115;
            _1499_onOwned = _out116;
            _1500_recIdents = _out117;
            RAST._IExpr _source73 = _1498_onExpr;
            {
              bool disjunctiveMatch10 = false;
              if (_source73.is_Call) {
                RAST._IExpr obj2 = _source73.dtor_obj;
                if (obj2.is_Select) {
                  RAST._IExpr obj3 = obj2.dtor_obj;
                  if (obj3.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name11 = obj3.dtor_name;
                    if (object.Equals(name11, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      Dafny.ISequence<Dafny.Rune> name12 = obj2.dtor_name;
                      if (object.Equals(name12, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))) {
                        disjunctiveMatch10 = true;
                      }
                    }
                  }
                }
              }
              if (_source73.is_Identifier) {
                Dafny.ISequence<Dafny.Rune> name13 = _source73.dtor_name;
                if (object.Equals(name13, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                  disjunctiveMatch10 = true;
                }
              }
              if (_source73.is_UnaryOp) {
                Dafny.ISequence<Dafny.Rune> op14 = _source73.dtor_op1;
                if (object.Equals(op14, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                  RAST._IExpr underlying4 = _source73.dtor_underlying;
                  if (underlying4.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name14 = underlying4.dtor_name;
                    if (object.Equals(name14, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      disjunctiveMatch10 = true;
                    }
                  }
                }
              }
              if (disjunctiveMatch10) {
                Dafny.ISequence<Dafny.Rune> _1501_isAssignedVar;
                _1501_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1497_fieldName);
                if (((newEnv).dtor_names).Contains(_1501_isAssignedVar)) {
                  generated = ((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1497_fieldName), RAST.Expr.create_Identifier(_1501_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1501_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _1501_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _1497_fieldName, rhs);
                }
                goto after_match20;
              }
            }
            {
              if (!object.Equals(_1498_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _1498_onExpr = ((this).modify__macro).Apply1(_1498_onExpr);
              }
              generated = RAST.__default.AssignMember(_1498_onExpr, _1497_fieldName, rhs);
            }
          after_match20: ;
            readIdents = _1500_recIdents;
            needsIIFE = false;
          }
          goto after_match19;
        }
      }
      {
        DAST._IExpression _1502_on = _source72.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1503_indices = _source72.dtor_indices;
        {
          RAST._IExpr _1504_onExpr;
          DCOMP._IOwnership _1505_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1506_recIdents;
          RAST._IExpr _out118;
          DCOMP._IOwnership _out119;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out120;
          (this).GenExpr(_1502_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out118, out _out119, out _out120);
          _1504_onExpr = _out118;
          _1505_onOwned = _out119;
          _1506_recIdents = _out120;
          readIdents = _1506_recIdents;
          _1504_onExpr = ((this).modify__macro).Apply1(_1504_onExpr);
          RAST._IExpr _1507_r;
          _1507_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1508_indicesExpr;
          _1508_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi32 = new BigInteger((_1503_indices).Count);
          for (BigInteger _1509_i = BigInteger.Zero; _1509_i < _hi32; _1509_i++) {
            RAST._IExpr _1510_idx;
            DCOMP._IOwnership _1511___v79;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1512_recIdentsIdx;
            RAST._IExpr _out121;
            DCOMP._IOwnership _out122;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out123;
            (this).GenExpr((_1503_indices).Select(_1509_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out121, out _out122, out _out123);
            _1510_idx = _out121;
            _1511___v79 = _out122;
            _1512_recIdentsIdx = _out123;
            Dafny.ISequence<Dafny.Rune> _1513_varName;
            _1513_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1509_i));
            _1508_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1508_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1513_varName)));
            _1507_r = (_1507_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1513_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.IntoUsize(_1510_idx))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1512_recIdentsIdx);
          }
          if ((new BigInteger((_1503_indices).Count)) > (BigInteger.One)) {
            _1504_onExpr = (_1504_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1514_rhs;
          _1514_rhs = rhs;
          var _pat_let_tv3 = env;
          if (((_1504_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1504_onExpr).LhsIdentifierName(), _pat_let32_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let32_0, _1515_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv3).GetType(_1515_name), _pat_let33_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let33_0, _1516_tpe => ((_1516_tpe).is_Some) && (((_1516_tpe).dtor_value).IsUninitArray())))))))) {
            _1514_rhs = RAST.__default.MaybeUninitNew(_1514_rhs);
          }
          generated = (_1507_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1504_onExpr, _1508_indicesExpr)), _1514_rhs));
          needsIIFE = true;
        }
      }
    after_match19: ;
    }
    public void GenStmt(DAST._IStatement stmt, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source74 = stmt;
      {
        if (_source74.is_ConstructorNewSeparator) {
          Dafny.ISequence<DAST._IFormal> _1517_fields = _source74.dtor_fields;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi33 = new BigInteger((_1517_fields).Count);
            for (BigInteger _1518_i = BigInteger.Zero; _1518_i < _hi33; _1518_i++) {
              DAST._IFormal _1519_field;
              _1519_field = (_1517_fields).Select(_1518_i);
              Dafny.ISequence<Dafny.Rune> _1520_fieldName;
              _1520_fieldName = DCOMP.__default.escapeName((_1519_field).dtor_name);
              RAST._IType _1521_fieldTyp;
              RAST._IType _out124;
              _out124 = (this).GenType((_1519_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _1521_fieldTyp = _out124;
              Dafny.ISequence<Dafny.Rune> _1522_isAssignedVar;
              _1522_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1520_fieldName);
              if (((newEnv).dtor_names).Contains(_1522_isAssignedVar)) {
                RAST._IExpr _1523_rhs;
                DCOMP._IOwnership _1524___v80;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1525___v81;
                RAST._IExpr _out125;
                DCOMP._IOwnership _out126;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out127;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1519_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out125, out _out126, out _out127);
                _1523_rhs = _out125;
                _1524___v80 = _out126;
                _1525___v81 = _out127;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1522_isAssignedVar));
                generated = (generated).Then(((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1520_fieldName), RAST.Expr.create_Identifier(_1522_isAssignedVar), _1523_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1522_isAssignedVar);
              }
            }
          }
          goto after_match21;
        }
      }
      {
        if (_source74.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1526_name = _source74.dtor_name;
          DAST._IType _1527_typ = _source74.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source74.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1528_expression = maybeValue1.dtor_value;
            {
              RAST._IType _1529_tpe;
              RAST._IType _out128;
              _out128 = (this).GenType(_1527_typ, DCOMP.GenTypeContext.InBinding());
              _1529_tpe = _out128;
              Dafny.ISequence<Dafny.Rune> _1530_varName;
              _1530_varName = DCOMP.__default.escapeName(_1526_name);
              bool _1531_hasCopySemantics;
              _1531_hasCopySemantics = (_1529_tpe).CanReadWithoutClone();
              if (((_1528_expression).is_InitializationValue) && (!(_1531_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1530_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).ApplyType1(_1529_tpe)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1530_varName, RAST.__default.MaybePlaceboType(_1529_tpe));
              } else {
                RAST._IExpr _1532_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1533_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1528_expression).is_InitializationValue) && ((_1529_tpe).IsObjectOrPointer())) {
                  _1532_expr = (_1529_tpe).ToNullExpr();
                  _1533_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1534_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out129;
                  DCOMP._IOwnership _out130;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
                  (this).GenExpr(_1528_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out129, out _out130, out _out131);
                  _1532_expr = _out129;
                  _1534_exprOwnership = _out130;
                  _1533_recIdents = _out131;
                }
                readIdents = _1533_recIdents;
                if ((_1528_expression).is_NewUninitArray) {
                  _1529_tpe = (_1529_tpe).TypeAtInitialization();
                } else {
                  _1529_tpe = _1529_tpe;
                }
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_1526_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1529_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1532_expr));
                newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_1526_name), _1529_tpe);
              }
            }
            goto after_match21;
          }
        }
      }
      {
        if (_source74.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1535_name = _source74.dtor_name;
          DAST._IType _1536_typ = _source74.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source74.dtor_maybeValue;
          if (maybeValue2.is_None) {
            {
              DAST._IStatement _1537_newStmt;
              _1537_newStmt = DAST.Statement.create_DeclareVar(_1535_name, _1536_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1536_typ)));
              RAST._IExpr _out132;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out133;
              DCOMP._IEnvironment _out134;
              (this).GenStmt(_1537_newStmt, selfIdent, env, isLast, earlyReturn, out _out132, out _out133, out _out134);
              generated = _out132;
              readIdents = _out133;
              newEnv = _out134;
            }
            goto after_match21;
          }
        }
      }
      {
        if (_source74.is_Assign) {
          DAST._IAssignLhs _1538_lhs = _source74.dtor_lhs;
          DAST._IExpression _1539_expression = _source74.dtor_value;
          {
            RAST._IExpr _1540_exprGen;
            DCOMP._IOwnership _1541___v82;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1542_exprIdents;
            RAST._IExpr _out135;
            DCOMP._IOwnership _out136;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
            (this).GenExpr(_1539_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out135, out _out136, out _out137);
            _1540_exprGen = _out135;
            _1541___v82 = _out136;
            _1542_exprIdents = _out137;
            if ((_1538_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1543_rustId;
              _1543_rustId = DCOMP.__default.escapeName(((_1538_lhs).dtor_ident));
              Std.Wrappers._IOption<RAST._IType> _1544_tpe;
              _1544_tpe = (env).GetType(_1543_rustId);
              if (((_1544_tpe).is_Some) && ((((_1544_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1540_exprGen = RAST.__default.MaybePlacebo(_1540_exprGen);
              }
            }
            if (((_1538_lhs).is_Index) && (((_1538_lhs).dtor_expr).is_Ident)) {
              Dafny.ISequence<Dafny.Rune> _1545_rustId;
              _1545_rustId = DCOMP.__default.escapeName(((_1538_lhs).dtor_expr).dtor_name);
              Std.Wrappers._IOption<RAST._IType> _1546_tpe;
              _1546_tpe = (env).GetType(_1545_rustId);
              if (((_1546_tpe).is_Some) && ((((_1546_tpe).dtor_value).ExtractMaybeUninitArrayElement()).is_Some)) {
                _1540_exprGen = RAST.__default.MaybeUninitNew(_1540_exprGen);
              }
            }
            RAST._IExpr _1547_lhsGen;
            bool _1548_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1549_recIdents;
            DCOMP._IEnvironment _1550_resEnv;
            RAST._IExpr _out138;
            bool _out139;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out140;
            DCOMP._IEnvironment _out141;
            (this).GenAssignLhs(_1538_lhs, _1540_exprGen, selfIdent, env, out _out138, out _out139, out _out140, out _out141);
            _1547_lhsGen = _out138;
            _1548_needsIIFE = _out139;
            _1549_recIdents = _out140;
            _1550_resEnv = _out141;
            generated = _1547_lhsGen;
            newEnv = _1550_resEnv;
            if (_1548_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1549_recIdents, _1542_exprIdents);
          }
          goto after_match21;
        }
      }
      {
        if (_source74.is_If) {
          DAST._IExpression _1551_cond = _source74.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1552_thnDafny = _source74.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1553_elsDafny = _source74.dtor_els;
          {
            RAST._IExpr _1554_cond;
            DCOMP._IOwnership _1555___v83;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1556_recIdents;
            RAST._IExpr _out142;
            DCOMP._IOwnership _out143;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
            (this).GenExpr(_1551_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out142, out _out143, out _out144);
            _1554_cond = _out142;
            _1555___v83 = _out143;
            _1556_recIdents = _out144;
            Dafny.ISequence<Dafny.Rune> _1557_condString;
            _1557_condString = (_1554_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1556_recIdents;
            RAST._IExpr _1558_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1559_thnIdents;
            DCOMP._IEnvironment _1560_thnEnv;
            RAST._IExpr _out145;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out146;
            DCOMP._IEnvironment _out147;
            (this).GenStmts(_1552_thnDafny, selfIdent, env, isLast, earlyReturn, out _out145, out _out146, out _out147);
            _1558_thn = _out145;
            _1559_thnIdents = _out146;
            _1560_thnEnv = _out147;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1559_thnIdents);
            RAST._IExpr _1561_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1562_elsIdents;
            DCOMP._IEnvironment _1563_elsEnv;
            RAST._IExpr _out148;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out149;
            DCOMP._IEnvironment _out150;
            (this).GenStmts(_1553_elsDafny, selfIdent, env, isLast, earlyReturn, out _out148, out _out149, out _out150);
            _1561_els = _out148;
            _1562_elsIdents = _out149;
            _1563_elsEnv = _out150;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1562_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1554_cond, _1558_thn, _1561_els);
          }
          goto after_match21;
        }
      }
      {
        if (_source74.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1564_lbl = _source74.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1565_body = _source74.dtor_body;
          {
            RAST._IExpr _1566_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1567_bodyIdents;
            DCOMP._IEnvironment _1568_env2;
            RAST._IExpr _out151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out152;
            DCOMP._IEnvironment _out153;
            (this).GenStmts(_1565_body, selfIdent, env, isLast, earlyReturn, out _out151, out _out152, out _out153);
            _1566_body = _out151;
            _1567_bodyIdents = _out152;
            _1568_env2 = _out153;
            readIdents = _1567_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1564_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1566_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
          goto after_match21;
        }
      }
      {
        if (_source74.is_While) {
          DAST._IExpression _1569_cond = _source74.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1570_body = _source74.dtor_body;
          {
            RAST._IExpr _1571_cond;
            DCOMP._IOwnership _1572___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1573_recIdents;
            RAST._IExpr _out154;
            DCOMP._IOwnership _out155;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
            (this).GenExpr(_1569_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out154, out _out155, out _out156);
            _1571_cond = _out154;
            _1572___v84 = _out155;
            _1573_recIdents = _out156;
            readIdents = _1573_recIdents;
            RAST._IExpr _1574_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1575_bodyIdents;
            DCOMP._IEnvironment _1576_bodyEnv;
            RAST._IExpr _out157;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out158;
            DCOMP._IEnvironment _out159;
            (this).GenStmts(_1570_body, selfIdent, env, false, earlyReturn, out _out157, out _out158, out _out159);
            _1574_bodyExpr = _out157;
            _1575_bodyIdents = _out158;
            _1576_bodyEnv = _out159;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1575_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1571_cond), _1574_bodyExpr);
          }
          goto after_match21;
        }
      }
      {
        if (_source74.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1577_boundName = _source74.dtor_boundName;
          DAST._IType _1578_boundType = _source74.dtor_boundType;
          DAST._IExpression _1579_overExpr = _source74.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1580_body = _source74.dtor_body;
          {
            RAST._IExpr _1581_over;
            DCOMP._IOwnership _1582___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1583_recIdents;
            RAST._IExpr _out160;
            DCOMP._IOwnership _out161;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out162;
            (this).GenExpr(_1579_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out160, out _out161, out _out162);
            _1581_over = _out160;
            _1582___v85 = _out161;
            _1583_recIdents = _out162;
            if (((_1579_overExpr).is_MapBoundedPool) || ((_1579_overExpr).is_SetBoundedPool)) {
              _1581_over = ((_1581_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1584_boundTpe;
            RAST._IType _out163;
            _out163 = (this).GenType(_1578_boundType, DCOMP.GenTypeContext.@default());
            _1584_boundTpe = _out163;
            readIdents = _1583_recIdents;
            Dafny.ISequence<Dafny.Rune> _1585_boundRName;
            _1585_boundRName = DCOMP.__default.escapeName(_1577_boundName);
            RAST._IExpr _1586_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1587_bodyIdents;
            DCOMP._IEnvironment _1588_bodyEnv;
            RAST._IExpr _out164;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out165;
            DCOMP._IEnvironment _out166;
            (this).GenStmts(_1580_body, selfIdent, (env).AddAssigned(_1585_boundRName, _1584_boundTpe), false, earlyReturn, out _out164, out _out165, out _out166);
            _1586_bodyExpr = _out164;
            _1587_bodyIdents = _out165;
            _1588_bodyEnv = _out166;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1587_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1585_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1585_boundRName, _1581_over, _1586_bodyExpr);
          }
          goto after_match21;
        }
      }
      {
        if (_source74.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1589_toLabel = _source74.dtor_toLabel;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source75 = _1589_toLabel;
            {
              if (_source75.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1590_lbl = _source75.dtor_value;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1590_lbl)));
                }
                goto after_match22;
              }
            }
            {
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
          after_match22: ;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match21;
        }
      }
      {
        if (_source74.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1591_body = _source74.dtor_body;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _1592_selfClone;
              DCOMP._IOwnership _1593___v86;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1594___v87;
              RAST._IExpr _out167;
              DCOMP._IOwnership _out168;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out169;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out167, out _out168, out _out169);
              _1592_selfClone = _out167;
              _1593___v86 = _out168;
              _1594___v87 = _out169;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1592_selfClone)));
            }
            newEnv = env;
            BigInteger _hi34 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1595_paramI = BigInteger.Zero; _1595_paramI < _hi34; _1595_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1596_param;
              _1596_param = ((env).dtor_names).Select(_1595_paramI);
              RAST._IExpr _1597_paramInit;
              DCOMP._IOwnership _1598___v88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1599___v89;
              RAST._IExpr _out170;
              DCOMP._IOwnership _out171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out172;
              (this).GenIdent(_1596_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out170, out _out171, out _out172);
              _1597_paramInit = _out170;
              _1598___v88 = _out171;
              _1599___v89 = _out172;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1596_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1597_paramInit)));
              if (((env).dtor_types).Contains(_1596_param)) {
                RAST._IType _1600_declaredType;
                _1600_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1596_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1596_param, _1600_declaredType);
              }
            }
            RAST._IExpr _1601_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1602_bodyIdents;
            DCOMP._IEnvironment _1603_bodyEnv;
            RAST._IExpr _out173;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out174;
            DCOMP._IEnvironment _out175;
            (this).GenStmts(_1591_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out173, out _out174, out _out175);
            _1601_bodyExpr = _out173;
            _1602_bodyIdents = _out174;
            _1603_bodyEnv = _out175;
            readIdents = _1602_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1601_bodyExpr)));
          }
          goto after_match21;
        }
      }
      {
        if (_source74.is_JumpTailCallStart) {
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match21;
        }
      }
      {
        if (_source74.is_Call) {
          DAST._IExpression _1604_on = _source74.dtor_on;
          DAST._ICallName _1605_name = _source74.dtor_callName;
          Dafny.ISequence<DAST._IType> _1606_typeArgs = _source74.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1607_args = _source74.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1608_maybeOutVars = _source74.dtor_outs;
          {
            Dafny.ISequence<RAST._IExpr> _1609_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1610_recIdents;
            Dafny.ISequence<RAST._IType> _1611_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _1612_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out176;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
            Dafny.ISequence<RAST._IType> _out178;
            Std.Wrappers._IOption<DAST._IResolvedType> _out179;
            (this).GenArgs(selfIdent, _1605_name, _1606_typeArgs, _1607_args, env, out _out176, out _out177, out _out178, out _out179);
            _1609_argExprs = _out176;
            _1610_recIdents = _out177;
            _1611_typeExprs = _out178;
            _1612_fullNameQualifier = _out179;
            readIdents = _1610_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source76 = _1612_fullNameQualifier;
            {
              if (_source76.is_Some) {
                DAST._IResolvedType value9 = _source76.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1613_path = value9.dtor_path;
                Dafny.ISequence<DAST._IType> _1614_onTypeArgs = value9.dtor_typeArgs;
                DAST._IResolvedTypeBase _1615_base = value9.dtor_kind;
                RAST._IExpr _1616_fullPath;
                RAST._IExpr _out180;
                _out180 = DCOMP.COMP.GenPathExpr(_1613_path);
                _1616_fullPath = _out180;
                Dafny.ISequence<RAST._IType> _1617_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out181;
                _out181 = (this).GenTypeArgs(_1614_onTypeArgs, DCOMP.GenTypeContext.@default());
                _1617_onTypeExprs = _out181;
                RAST._IExpr _1618_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _1619_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1620_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1615_base).is_Trait) || ((_1615_base).is_Class)) {
                  RAST._IExpr _out182;
                  DCOMP._IOwnership _out183;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out184;
                  (this).GenExpr(_1604_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out182, out _out183, out _out184);
                  _1618_onExpr = _out182;
                  _1619_recOwnership = _out183;
                  _1620_recIdents = _out184;
                  _1618_onExpr = ((this).modify__macro).Apply1(_1618_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1620_recIdents);
                } else {
                  RAST._IExpr _out185;
                  DCOMP._IOwnership _out186;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out187;
                  (this).GenExpr(_1604_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out185, out _out186, out _out187);
                  _1618_onExpr = _out185;
                  _1619_recOwnership = _out186;
                  _1620_recIdents = _out187;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1620_recIdents);
                }
                generated = ((((_1616_fullPath).ApplyType(_1617_onTypeExprs)).MSel(DCOMP.__default.escapeName((_1605_name).dtor_name))).ApplyType(_1611_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_1618_onExpr), _1609_argExprs));
                goto after_match23;
              }
            }
            {
              RAST._IExpr _1621_onExpr;
              DCOMP._IOwnership _1622___v94;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1623_enclosingIdents;
              RAST._IExpr _out188;
              DCOMP._IOwnership _out189;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out190;
              (this).GenExpr(_1604_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out188, out _out189, out _out190);
              _1621_onExpr = _out188;
              _1622___v94 = _out189;
              _1623_enclosingIdents = _out190;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1623_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _1624_renderedName;
              DAST._ICallName _source77 = _1605_name;
              {
                if (_source77.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _1625_name = _source77.dtor_name;
                  _1624_renderedName = DCOMP.__default.escapeName(_1625_name);
                  goto after_match24;
                }
              }
              {
                bool disjunctiveMatch11 = false;
                if (_source77.is_MapBuilderAdd) {
                  disjunctiveMatch11 = true;
                }
                if (_source77.is_SetBuilderAdd) {
                  disjunctiveMatch11 = true;
                }
                if (disjunctiveMatch11) {
                  _1624_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                  goto after_match24;
                }
              }
              {
                _1624_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
              }
            after_match24: ;
              DAST._IExpression _source78 = _1604_on;
              {
                if (_source78.is_Companion) {
                  {
                    _1621_onExpr = (_1621_onExpr).MSel(_1624_renderedName);
                  }
                  goto after_match25;
                }
              }
              {
                {
                  if (!object.Equals(_1621_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source79 = _1605_name;
                    {
                      if (_source79.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source79.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _1626_tpe = onType0.dtor_value;
                          RAST._IType _1627_typ;
                          RAST._IType _out191;
                          _out191 = (this).GenType(_1626_tpe, DCOMP.GenTypeContext.@default());
                          _1627_typ = _out191;
                          if (((_1627_typ).IsObjectOrPointer()) && (!object.Equals(_1621_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _1621_onExpr = ((this).modify__macro).Apply1(_1621_onExpr);
                          }
                          goto after_match26;
                        }
                      }
                    }
                    {
                    }
                  after_match26: ;
                  }
                  _1621_onExpr = (_1621_onExpr).Sel(_1624_renderedName);
                }
              }
            after_match25: ;
              generated = ((_1621_onExpr).ApplyType(_1611_typeExprs)).Apply(_1609_argExprs);
            }
          after_match23: ;
            if (((_1608_maybeOutVars).is_Some) && ((new BigInteger(((_1608_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1628_outVar;
              _1628_outVar = DCOMP.__default.escapeName((((_1608_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
              if (!((env).CanReadWithoutClone(_1628_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1628_outVar, generated);
            } else if (((_1608_maybeOutVars).is_None) || ((new BigInteger(((_1608_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1629_tmpVar;
              _1629_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1630_tmpId;
              _1630_tmpId = RAST.Expr.create_Identifier(_1629_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1629_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1631_outVars;
              _1631_outVars = (_1608_maybeOutVars).dtor_value;
              BigInteger _hi35 = new BigInteger((_1631_outVars).Count);
              for (BigInteger _1632_outI = BigInteger.Zero; _1632_outI < _hi35; _1632_outI++) {
                Dafny.ISequence<Dafny.Rune> _1633_outVar;
                _1633_outVar = DCOMP.__default.escapeName(((_1631_outVars).Select(_1632_outI)));
                RAST._IExpr _1634_rhs;
                _1634_rhs = (_1630_tmpId).Sel(Std.Strings.__default.OfNat(_1632_outI));
                if (!((env).CanReadWithoutClone(_1633_outVar))) {
                  _1634_rhs = RAST.__default.MaybePlacebo(_1634_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1633_outVar, _1634_rhs));
              }
            }
            newEnv = env;
          }
          goto after_match21;
        }
      }
      {
        if (_source74.is_Return) {
          DAST._IExpression _1635_exprDafny = _source74.dtor_expr;
          {
            RAST._IExpr _1636_expr;
            DCOMP._IOwnership _1637___v105;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1638_recIdents;
            RAST._IExpr _out192;
            DCOMP._IOwnership _out193;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out194;
            (this).GenExpr(_1635_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out192, out _out193, out _out194);
            _1636_expr = _out192;
            _1637___v105 = _out193;
            _1638_recIdents = _out194;
            readIdents = _1638_recIdents;
            if (isLast) {
              generated = _1636_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1636_expr));
            }
            newEnv = env;
          }
          goto after_match21;
        }
      }
      {
        if (_source74.is_EarlyReturn) {
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source80 = earlyReturn;
            {
              if (_source80.is_None) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
                goto after_match27;
              }
            }
            {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1639_rustIdents = _source80.dtor_value;
              Dafny.ISequence<RAST._IExpr> _1640_tupleArgs;
              _1640_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi36 = new BigInteger((_1639_rustIdents).Count);
              for (BigInteger _1641_i = BigInteger.Zero; _1641_i < _hi36; _1641_i++) {
                RAST._IExpr _1642_rIdent;
                DCOMP._IOwnership _1643___v106;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1644___v107;
                RAST._IExpr _out195;
                DCOMP._IOwnership _out196;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out197;
                (this).GenIdent((_1639_rustIdents).Select(_1641_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out195, out _out196, out _out197);
                _1642_rIdent = _out195;
                _1643___v106 = _out196;
                _1644___v107 = _out197;
                _1640_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1640_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1642_rIdent));
              }
              if ((new BigInteger((_1640_tupleArgs).Count)) == (BigInteger.One)) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1640_tupleArgs).Select(BigInteger.Zero)));
              } else {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1640_tupleArgs)));
              }
            }
          after_match27: ;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match21;
        }
      }
      {
        if (_source74.is_Halt) {
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match21;
        }
      }
      {
        DAST._IExpression _1645_e = _source74.dtor_Print_a0;
        {
          RAST._IExpr _1646_printedExpr;
          DCOMP._IOwnership _1647_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1648_recIdents;
          RAST._IExpr _out198;
          DCOMP._IOwnership _out199;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out200;
          (this).GenExpr(_1645_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out198, out _out199, out _out200);
          _1646_printedExpr = _out198;
          _1647_recOwnership = _out199;
          _1648_recIdents = _out200;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1646_printedExpr)));
          readIdents = _1648_recIdents;
          newEnv = env;
        }
      }
    after_match21: ;
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source81 = range;
      {
        if (_source81.is_NoRange) {
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      {
        if (_source81.is_U8) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      {
        if (_source81.is_U16) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      {
        if (_source81.is_U32) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      {
        if (_source81.is_U64) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      {
        if (_source81.is_U128) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      {
        if (_source81.is_I8) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      {
        if (_source81.is_I16) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      {
        if (_source81.is_I32) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      {
        if (_source81.is_I64) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      {
        if (_source81.is_I128) {
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
      DAST._IExpression _source82 = e;
      {
        if (_source82.is_Literal) {
          DAST._ILiteral _h170 = _source82.dtor_Literal_a0;
          if (_h170.is_BoolLiteral) {
            bool _1649_b = _h170.dtor_BoolLiteral_a0;
            {
              RAST._IExpr _out205;
              DCOMP._IOwnership _out206;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_1649_b), expectedOwnership, out _out205, out _out206);
              r = _out205;
              resultingOwnership = _out206;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match28;
          }
        }
      }
      {
        if (_source82.is_Literal) {
          DAST._ILiteral _h171 = _source82.dtor_Literal_a0;
          if (_h171.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1650_i = _h171.dtor_IntLiteral_a0;
            DAST._IType _1651_t = _h171.dtor_IntLiteral_a1;
            {
              DAST._IType _source83 = _1651_t;
              {
                if (_source83.is_Primitive) {
                  DAST._IPrimitive _h70 = _source83.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    {
                      if ((new BigInteger((_1650_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1650_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1650_i, true, false));
                      }
                    }
                    goto after_match29;
                  }
                }
              }
              {
                DAST._IType _1652_o = _source83;
                {
                  RAST._IType _1653_genType;
                  RAST._IType _out207;
                  _out207 = (this).GenType(_1652_o, DCOMP.GenTypeContext.@default());
                  _1653_genType = _out207;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1650_i), _1653_genType);
                }
              }
            after_match29: ;
              RAST._IExpr _out208;
              DCOMP._IOwnership _out209;
              (this).FromOwned(r, expectedOwnership, out _out208, out _out209);
              r = _out208;
              resultingOwnership = _out209;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match28;
          }
        }
      }
      {
        if (_source82.is_Literal) {
          DAST._ILiteral _h172 = _source82.dtor_Literal_a0;
          if (_h172.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1654_n = _h172.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1655_d = _h172.dtor_DecLiteral_a1;
            DAST._IType _1656_t = _h172.dtor_DecLiteral_a2;
            {
              DAST._IType _source84 = _1656_t;
              {
                if (_source84.is_Primitive) {
                  DAST._IPrimitive _h71 = _source84.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1654_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1655_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                    goto after_match30;
                  }
                }
              }
              {
                DAST._IType _1657_o = _source84;
                {
                  RAST._IType _1658_genType;
                  RAST._IType _out210;
                  _out210 = (this).GenType(_1657_o, DCOMP.GenTypeContext.@default());
                  _1658_genType = _out210;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1654_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1655_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1658_genType);
                }
              }
            after_match30: ;
              RAST._IExpr _out211;
              DCOMP._IOwnership _out212;
              (this).FromOwned(r, expectedOwnership, out _out211, out _out212);
              r = _out211;
              resultingOwnership = _out212;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match28;
          }
        }
      }
      {
        if (_source82.is_Literal) {
          DAST._ILiteral _h173 = _source82.dtor_Literal_a0;
          if (_h173.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1659_l = _h173.dtor_StringLiteral_a0;
            bool _1660_verbatim = _h173.dtor_verbatim;
            {
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1659_l, false, _1660_verbatim));
              RAST._IExpr _out213;
              DCOMP._IOwnership _out214;
              (this).FromOwned(r, expectedOwnership, out _out213, out _out214);
              r = _out213;
              resultingOwnership = _out214;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match28;
          }
        }
      }
      {
        if (_source82.is_Literal) {
          DAST._ILiteral _h174 = _source82.dtor_Literal_a0;
          if (_h174.is_CharLiteralUTF16) {
            BigInteger _1661_c = _h174.dtor_CharLiteralUTF16_a0;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1661_c));
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
            goto after_match28;
          }
        }
      }
      {
        if (_source82.is_Literal) {
          DAST._ILiteral _h175 = _source82.dtor_Literal_a0;
          if (_h175.is_CharLiteral) {
            Dafny.Rune _1662_c = _h175.dtor_CharLiteral_a0;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1662_c).Value)));
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
            goto after_match28;
          }
        }
      }
      {
        DAST._ILiteral _h176 = _source82.dtor_Literal_a0;
        DAST._IType _1663_tpe = _h176.dtor_Null_a0;
        {
          RAST._IType _1664_tpeGen;
          RAST._IType _out219;
          _out219 = (this).GenType(_1663_tpe, DCOMP.GenTypeContext.@default());
          _1664_tpeGen = _out219;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null"));
          } else {
            r = RAST.Expr.create_TypeAscription(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _1664_tpeGen);
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
    after_match28: ;
    }
    public void GenExprBinary(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IBinOp _1665_op = _let_tmp_rhs54.dtor_op;
      DAST._IExpression _1666_lExpr = _let_tmp_rhs54.dtor_left;
      DAST._IExpression _1667_rExpr = _let_tmp_rhs54.dtor_right;
      DAST.Format._IBinaryOpFormat _1668_format = _let_tmp_rhs54.dtor_format2;
      bool _1669_becomesLeftCallsRight;
      DAST._IBinOp _source85 = _1665_op;
      {
        bool disjunctiveMatch12 = false;
        if (_source85.is_SetMerge) {
          disjunctiveMatch12 = true;
        }
        if (_source85.is_SetSubtraction) {
          disjunctiveMatch12 = true;
        }
        if (_source85.is_SetIntersection) {
          disjunctiveMatch12 = true;
        }
        if (_source85.is_SetDisjoint) {
          disjunctiveMatch12 = true;
        }
        if (_source85.is_MapMerge) {
          disjunctiveMatch12 = true;
        }
        if (_source85.is_MapSubtraction) {
          disjunctiveMatch12 = true;
        }
        if (_source85.is_MultisetMerge) {
          disjunctiveMatch12 = true;
        }
        if (_source85.is_MultisetSubtraction) {
          disjunctiveMatch12 = true;
        }
        if (_source85.is_MultisetIntersection) {
          disjunctiveMatch12 = true;
        }
        if (_source85.is_MultisetDisjoint) {
          disjunctiveMatch12 = true;
        }
        if (_source85.is_Concat) {
          disjunctiveMatch12 = true;
        }
        if (disjunctiveMatch12) {
          _1669_becomesLeftCallsRight = true;
          goto after_match31;
        }
      }
      {
        _1669_becomesLeftCallsRight = false;
      }
    after_match31: ;
      bool _1670_becomesRightCallsLeft;
      DAST._IBinOp _source86 = _1665_op;
      {
        if (_source86.is_In) {
          _1670_becomesRightCallsLeft = true;
          goto after_match32;
        }
      }
      {
        _1670_becomesRightCallsLeft = false;
      }
    after_match32: ;
      bool _1671_becomesCallLeftRight;
      DAST._IBinOp _source87 = _1665_op;
      {
        if (_source87.is_Eq) {
          bool referential0 = _source87.dtor_referential;
          if ((referential0) == (true)) {
            _1671_becomesCallLeftRight = false;
            goto after_match33;
          }
        }
      }
      {
        if (_source87.is_SetMerge) {
          _1671_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_SetSubtraction) {
          _1671_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_SetIntersection) {
          _1671_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_SetDisjoint) {
          _1671_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_MapMerge) {
          _1671_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_MapSubtraction) {
          _1671_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_MultisetMerge) {
          _1671_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_MultisetSubtraction) {
          _1671_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_MultisetIntersection) {
          _1671_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_MultisetDisjoint) {
          _1671_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_Concat) {
          _1671_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        _1671_becomesCallLeftRight = false;
      }
    after_match33: ;
      DCOMP._IOwnership _1672_expectedLeftOwnership;
      if (_1669_becomesLeftCallsRight) {
        _1672_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipAutoBorrowed();
      } else if ((_1670_becomesRightCallsLeft) || (_1671_becomesCallLeftRight)) {
        _1672_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        _1672_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipOwned();
      }
      DCOMP._IOwnership _1673_expectedRightOwnership;
      if ((_1669_becomesLeftCallsRight) || (_1671_becomesCallLeftRight)) {
        _1673_expectedRightOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else if (_1670_becomesRightCallsLeft) {
        _1673_expectedRightOwnership = DCOMP.Ownership.create_OwnershipAutoBorrowed();
      } else {
        _1673_expectedRightOwnership = DCOMP.Ownership.create_OwnershipOwned();
      }
      RAST._IExpr _1674_left;
      DCOMP._IOwnership _1675___v112;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1676_recIdentsL;
      RAST._IExpr _out222;
      DCOMP._IOwnership _out223;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out224;
      (this).GenExpr(_1666_lExpr, selfIdent, env, _1672_expectedLeftOwnership, out _out222, out _out223, out _out224);
      _1674_left = _out222;
      _1675___v112 = _out223;
      _1676_recIdentsL = _out224;
      RAST._IExpr _1677_right;
      DCOMP._IOwnership _1678___v113;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1679_recIdentsR;
      RAST._IExpr _out225;
      DCOMP._IOwnership _out226;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out227;
      (this).GenExpr(_1667_rExpr, selfIdent, env, _1673_expectedRightOwnership, out _out225, out _out226, out _out227);
      _1677_right = _out225;
      _1678___v113 = _out226;
      _1679_recIdentsR = _out227;
      DAST._IBinOp _source88 = _1665_op;
      {
        if (_source88.is_In) {
          {
            r = ((_1677_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1674_left);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_SeqProperPrefix) {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1674_left, _1677_right, _1668_format);
          goto after_match34;
        }
      }
      {
        if (_source88.is_SeqPrefix) {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1674_left, _1677_right, _1668_format);
          goto after_match34;
        }
      }
      {
        if (_source88.is_SetMerge) {
          {
            r = ((_1674_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1677_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_SetSubtraction) {
          {
            r = ((_1674_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1677_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_SetIntersection) {
          {
            r = ((_1674_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1677_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_Subset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1674_left, _1677_right, _1668_format);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_ProperSubset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1674_left, _1677_right, _1668_format);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_SetDisjoint) {
          {
            r = ((_1674_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1677_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_MapMerge) {
          {
            r = ((_1674_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1677_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_MapSubtraction) {
          {
            r = ((_1674_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1677_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_MultisetMerge) {
          {
            r = ((_1674_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1677_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_MultisetSubtraction) {
          {
            r = ((_1674_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1677_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_MultisetIntersection) {
          {
            r = ((_1674_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1677_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_Submultiset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1674_left, _1677_right, _1668_format);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_ProperSubmultiset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1674_left, _1677_right, _1668_format);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_MultisetDisjoint) {
          {
            r = ((_1674_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1677_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_Concat) {
          {
            r = ((_1674_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1677_right);
          }
          goto after_match34;
        }
      }
      {
        {
          if ((DCOMP.COMP.OpTable).Contains(_1665_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1665_op), _1674_left, _1677_right, _1668_format);
          } else {
            DAST._IBinOp _source89 = _1665_op;
            {
              if (_source89.is_Eq) {
                bool _1680_referential = _source89.dtor_referential;
                {
                  if (_1680_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1674_left, _1677_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_1667_rExpr).is_SeqValue) && ((new BigInteger(((_1667_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1674_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1666_lExpr).is_SeqValue) && ((new BigInteger(((_1666_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1677_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1674_left, _1677_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
                goto after_match35;
              }
            }
            {
              if (_source89.is_EuclidianDiv) {
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1674_left, _1677_right));
                }
                goto after_match35;
              }
            }
            {
              if (_source89.is_EuclidianMod) {
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1674_left, _1677_right));
                }
                goto after_match35;
              }
            }
            {
              Dafny.ISequence<Dafny.Rune> _1681_op = _source89.dtor_Passthrough_a0;
              {
                r = RAST.Expr.create_BinaryOp(_1681_op, _1674_left, _1677_right, _1668_format);
              }
            }
          after_match35: ;
          }
        }
      }
    after_match34: ;
      RAST._IExpr _out228;
      DCOMP._IOwnership _out229;
      (this).FromOwned(r, expectedOwnership, out _out228, out _out229);
      r = _out228;
      resultingOwnership = _out229;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1676_recIdentsL, _1679_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _1682_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _1683_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _1684_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _1684_toTpe;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1685_path = _let_tmp_rhs57.dtor_path;
      Dafny.ISequence<DAST._IType> _1686_typeArgs = _let_tmp_rhs57.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs58 = _let_tmp_rhs57.dtor_kind;
      DAST._IType _1687_b = _let_tmp_rhs58.dtor_baseType;
      DAST._INewtypeRange _1688_range = _let_tmp_rhs58.dtor_range;
      bool _1689_erase = _let_tmp_rhs58.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1690___v115 = _let_tmp_rhs57.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1691___v116 = _let_tmp_rhs57.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1692___v117 = _let_tmp_rhs57.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1693_nativeToType;
      _1693_nativeToType = DCOMP.COMP.NewtypeToRustType(_1687_b, _1688_range);
      if (object.Equals(_1683_fromTpe, _1687_b)) {
        RAST._IExpr _1694_recursiveGen;
        DCOMP._IOwnership _1695_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1696_recIdents;
        RAST._IExpr _out230;
        DCOMP._IOwnership _out231;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out232;
        (this).GenExpr(_1682_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out230, out _out231, out _out232);
        _1694_recursiveGen = _out230;
        _1695_recOwned = _out231;
        _1696_recIdents = _out232;
        readIdents = _1696_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source90 = _1693_nativeToType;
        {
          if (_source90.is_Some) {
            RAST._IType _1697_v = _source90.dtor_value;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1694_recursiveGen, RAST.Expr.create_ExprFromType(_1697_v)));
            RAST._IExpr _out233;
            DCOMP._IOwnership _out234;
            (this).FromOwned(r, expectedOwnership, out _out233, out _out234);
            r = _out233;
            resultingOwnership = _out234;
            goto after_match36;
          }
        }
        {
          if (_1689_erase) {
            r = _1694_recursiveGen;
          } else {
            RAST._IType _1698_rhsType;
            RAST._IType _out235;
            _out235 = (this).GenType(_1684_toTpe, DCOMP.GenTypeContext.InBinding());
            _1698_rhsType = _out235;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1698_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1694_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out236;
          DCOMP._IOwnership _out237;
          (this).FromOwnership(r, _1695_recOwned, expectedOwnership, out _out236, out _out237);
          r = _out236;
          resultingOwnership = _out237;
        }
      after_match36: ;
      } else {
        if ((_1693_nativeToType).is_Some) {
          DAST._IType _source91 = _1683_fromTpe;
          {
            if (_source91.is_UserDefined) {
              DAST._IResolvedType resolved1 = _source91.dtor_resolved;
              DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
              if (kind1.is_Newtype) {
                DAST._IType _1699_b0 = kind1.dtor_baseType;
                DAST._INewtypeRange _1700_range0 = kind1.dtor_range;
                bool _1701_erase0 = kind1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1702_attributes0 = resolved1.dtor_attributes;
                {
                  Std.Wrappers._IOption<RAST._IType> _1703_nativeFromType;
                  _1703_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1699_b0, _1700_range0);
                  if ((_1703_nativeFromType).is_Some) {
                    RAST._IExpr _1704_recursiveGen;
                    DCOMP._IOwnership _1705_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1706_recIdents;
                    RAST._IExpr _out238;
                    DCOMP._IOwnership _out239;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out240;
                    (this).GenExpr(_1682_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out238, out _out239, out _out240);
                    _1704_recursiveGen = _out238;
                    _1705_recOwned = _out239;
                    _1706_recIdents = _out240;
                    RAST._IExpr _out241;
                    DCOMP._IOwnership _out242;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_1704_recursiveGen, (_1693_nativeToType).dtor_value), _1705_recOwned, expectedOwnership, out _out241, out _out242);
                    r = _out241;
                    resultingOwnership = _out242;
                    readIdents = _1706_recIdents;
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
          if (object.Equals(_1683_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1707_recursiveGen;
            DCOMP._IOwnership _1708_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1709_recIdents;
            RAST._IExpr _out243;
            DCOMP._IOwnership _out244;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out245;
            (this).GenExpr(_1682_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out243, out _out244, out _out245);
            _1707_recursiveGen = _out243;
            _1708_recOwned = _out244;
            _1709_recIdents = _out245;
            RAST._IExpr _out246;
            DCOMP._IOwnership _out247;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_1707_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1693_nativeToType).dtor_value), _1708_recOwned, expectedOwnership, out _out246, out _out247);
            r = _out246;
            resultingOwnership = _out247;
            readIdents = _1709_recIdents;
            return ;
          }
        }
        RAST._IExpr _out248;
        DCOMP._IOwnership _out249;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out250;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1682_expr, _1683_fromTpe, _1687_b), _1687_b, _1684_toTpe), selfIdent, env, expectedOwnership, out _out248, out _out249, out _out250);
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
      DAST._IExpression _1710_expr = _let_tmp_rhs59.dtor_value;
      DAST._IType _1711_fromTpe = _let_tmp_rhs59.dtor_from;
      DAST._IType _1712_toTpe = _let_tmp_rhs59.dtor_typ;
      DAST._IType _let_tmp_rhs60 = _1711_fromTpe;
      DAST._IResolvedType _let_tmp_rhs61 = _let_tmp_rhs60.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1713___v123 = _let_tmp_rhs61.dtor_path;
      Dafny.ISequence<DAST._IType> _1714___v124 = _let_tmp_rhs61.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs62 = _let_tmp_rhs61.dtor_kind;
      DAST._IType _1715_b = _let_tmp_rhs62.dtor_baseType;
      DAST._INewtypeRange _1716_range = _let_tmp_rhs62.dtor_range;
      bool _1717_erase = _let_tmp_rhs62.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1718_attributes = _let_tmp_rhs61.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1719___v125 = _let_tmp_rhs61.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1720___v126 = _let_tmp_rhs61.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1721_nativeFromType;
      _1721_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1715_b, _1716_range);
      if (object.Equals(_1715_b, _1712_toTpe)) {
        RAST._IExpr _1722_recursiveGen;
        DCOMP._IOwnership _1723_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1724_recIdents;
        RAST._IExpr _out251;
        DCOMP._IOwnership _out252;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out253;
        (this).GenExpr(_1710_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out251, out _out252, out _out253);
        _1722_recursiveGen = _out251;
        _1723_recOwned = _out252;
        _1724_recIdents = _out253;
        readIdents = _1724_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source92 = _1721_nativeFromType;
        {
          if (_source92.is_Some) {
            RAST._IType _1725_v = _source92.dtor_value;
            RAST._IType _1726_toTpeRust;
            RAST._IType _out254;
            _out254 = (this).GenType(_1712_toTpe, DCOMP.GenTypeContext.@default());
            _1726_toTpeRust = _out254;
            r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1726_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1722_recursiveGen));
            RAST._IExpr _out255;
            DCOMP._IOwnership _out256;
            (this).FromOwned(r, expectedOwnership, out _out255, out _out256);
            r = _out255;
            resultingOwnership = _out256;
            goto after_match38;
          }
        }
        {
          if (_1717_erase) {
            r = _1722_recursiveGen;
          } else {
            r = (_1722_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out257;
          DCOMP._IOwnership _out258;
          (this).FromOwnership(r, _1723_recOwned, expectedOwnership, out _out257, out _out258);
          r = _out257;
          resultingOwnership = _out258;
        }
      after_match38: ;
      } else {
        if ((_1721_nativeFromType).is_Some) {
          if (object.Equals(_1712_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1727_recursiveGen;
            DCOMP._IOwnership _1728_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1729_recIdents;
            RAST._IExpr _out259;
            DCOMP._IOwnership _out260;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out261;
            (this).GenExpr(_1710_expr, selfIdent, env, expectedOwnership, out _out259, out _out260, out _out261);
            _1727_recursiveGen = _out259;
            _1728_recOwned = _out260;
            _1729_recIdents = _out261;
            RAST._IExpr _out262;
            DCOMP._IOwnership _out263;
            (this).FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1727_recursiveGen, (this).DafnyCharUnderlying)), _1728_recOwned, expectedOwnership, out _out262, out _out263);
            r = _out262;
            resultingOwnership = _out263;
            readIdents = _1729_recIdents;
            return ;
          }
        }
        RAST._IExpr _out264;
        DCOMP._IOwnership _out265;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out266;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1710_expr, _1711_fromTpe, _1715_b), _1715_b, _1712_toTpe), selfIdent, env, expectedOwnership, out _out264, out _out265, out _out266);
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
        Std.Wrappers._IResult<__T, __E> _1730_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_1730_valueOrError0).IsFailure()) {
          return (_1730_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1731_head = (_1730_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _1732_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_1732_valueOrError1).IsFailure()) {
            return (_1732_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _1733_tail = (_1732_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1731_head), _1733_tail));
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
          RAST._IType _1734_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          RAST._IType _1735_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel((this).upcast)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1734_fromTpeUnderlying, _1735_toTpeUnderlying))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1736_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_1736_valueOrError0).IsFailure()) {
          return (_1736_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1737_lambda = (_1736_valueOrError0).Extract();
          if ((fromType).is_Arrow) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(_1737_lambda);
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).Apply1(_1737_lambda));
          }
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1738_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim12 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr12 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
          for (int i12 = 0; i12 < dim12; i12++) {
            var _1739_i = (BigInteger) i12;
            arr12[(int)(_1739_i)] = (this).UpcastConversionLambda((((fromType).dtor_resolved).dtor_typeArgs).Select(_1739_i), ((fromTpe).dtor_arguments).Select(_1739_i), (((toType).dtor_resolved).dtor_typeArgs).Select(_1739_i), ((toTpe).dtor_arguments).Select(_1739_i), typeParams);
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr12);
        }))());
        if ((_1738_valueOrError1).IsFailure()) {
          return (_1738_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _1740_lambdas = (_1738_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim13 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr13 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim13, "array size exceeds memory limit")];
  for (int i13 = 0; i13 < dim13; i13++) {
    var _1741_i = (BigInteger) i13;
    arr13[(int)(_1741_i)] = ((fromTpe).dtor_arguments).Select(_1741_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr13);
}))())).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_1740_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _1742_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _1743_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _1744_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _1745_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1746_valueOrError2 = (this).UpcastConversionLambda(_1744_newFromType, _1742_newFromTpe, _1745_newToType, _1743_newToTpe, typeParams);
        if ((_1746_valueOrError2).IsFailure()) {
          return (_1746_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1747_coerceArg = (_1746_valueOrError2).Extract();
          RAST._IExpr _1748_collectionType = (RAST.__default.dafny__runtime).MSel(((fromTpe).dtor_baseName).dtor_name);
          RAST._IExpr _1749_baseType = (((((fromTpe).dtor_baseName).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? ((_1748_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((fromTpe).dtor_arguments).Select(BigInteger.Zero), _1742_newFromTpe))) : ((_1748_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1742_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_1749_baseType).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_1747_coerceArg));
        }
      } else if ((((((((((fromTpe).is_DynType) && (((fromTpe).dtor_underlying).is_FnType)) && ((toTpe).is_DynType)) && (((toTpe).dtor_underlying).is_FnType)) && ((((fromTpe).dtor_underlying).dtor_arguments).Equals(((toTpe).dtor_underlying).dtor_arguments))) && ((fromType).is_Arrow)) && ((toType).is_Arrow)) && ((new BigInteger((((fromTpe).dtor_underlying).dtor_arguments).Count)) == (BigInteger.One))) && (((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).is_Borrowed)) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1750_valueOrError3 = (this).UpcastConversionLambda((fromType).dtor_result, ((fromTpe).dtor_underlying).dtor_returnType, (toType).dtor_result, ((toTpe).dtor_underlying).dtor_returnType, typeParams);
        if ((_1750_valueOrError3).IsFailure()) {
          return (_1750_valueOrError3).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1751_lambda = (_1750_valueOrError3).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn1_coerce"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying, ((fromTpe).dtor_underlying).dtor_returnType, ((toTpe).dtor_underlying).dtor_returnType))).Apply1(_1751_lambda));
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
      DAST._IExpression _1752_expr = _let_tmp_rhs63.dtor_value;
      DAST._IType _1753_fromTpe = _let_tmp_rhs63.dtor_from;
      DAST._IType _1754_toTpe = _let_tmp_rhs63.dtor_typ;
      RAST._IType _1755_fromTpeGen;
      RAST._IType _out267;
      _out267 = (this).GenType(_1753_fromTpe, DCOMP.GenTypeContext.InBinding());
      _1755_fromTpeGen = _out267;
      RAST._IType _1756_toTpeGen;
      RAST._IType _out268;
      _out268 = (this).GenType(_1754_toTpe, DCOMP.GenTypeContext.InBinding());
      _1756_toTpeGen = _out268;
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1757_upcastConverter;
      _1757_upcastConverter = (this).UpcastConversionLambda(_1753_fromTpe, _1755_fromTpeGen, _1754_toTpe, _1756_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_1757_upcastConverter).is_Success) {
        RAST._IExpr _1758_conversionLambda;
        _1758_conversionLambda = (_1757_upcastConverter).dtor_value;
        RAST._IExpr _1759_recursiveGen;
        DCOMP._IOwnership _1760_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1761_recIdents;
        RAST._IExpr _out269;
        DCOMP._IOwnership _out270;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out271;
        (this).GenExpr(_1752_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out269, out _out270, out _out271);
        _1759_recursiveGen = _out269;
        _1760_recOwned = _out270;
        _1761_recIdents = _out271;
        readIdents = _1761_recIdents;
        r = (_1758_conversionLambda).Apply1(_1759_recursiveGen);
        RAST._IExpr _out272;
        DCOMP._IOwnership _out273;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out272, out _out273);
        r = _out272;
        resultingOwnership = _out273;
      } else if ((this).IsDowncastConversion(_1755_fromTpeGen, _1756_toTpeGen)) {
        RAST._IExpr _1762_recursiveGen;
        DCOMP._IOwnership _1763_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1764_recIdents;
        RAST._IExpr _out274;
        DCOMP._IOwnership _out275;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out276;
        (this).GenExpr(_1752_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out274, out _out275, out _out276);
        _1762_recursiveGen = _out274;
        _1763_recOwned = _out275;
        _1764_recIdents = _out276;
        readIdents = _1764_recIdents;
        _1756_toTpeGen = (_1756_toTpeGen).ObjectOrPointerUnderlying();
        r = ((RAST.__default.dafny__runtime).MSel((this).downcast)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1762_recursiveGen, RAST.Expr.create_ExprFromType(_1756_toTpeGen)));
        RAST._IExpr _out277;
        DCOMP._IOwnership _out278;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out277, out _out278);
        r = _out277;
        resultingOwnership = _out278;
      } else {
        RAST._IExpr _1765_recursiveGen;
        DCOMP._IOwnership _1766_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1767_recIdents;
        RAST._IExpr _out279;
        DCOMP._IOwnership _out280;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out281;
        (this).GenExpr(_1752_expr, selfIdent, env, expectedOwnership, out _out279, out _out280, out _out281);
        _1765_recursiveGen = _out279;
        _1766_recOwned = _out280;
        _1767_recIdents = _out281;
        readIdents = _1767_recIdents;
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _let_tmp_rhs64 = _1757_upcastConverter;
        _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>> _let_tmp_rhs65 = _let_tmp_rhs64.dtor_error;
        DAST._IType _1768_fromType = _let_tmp_rhs65.dtor__0;
        RAST._IType _1769_fromTpeGen = _let_tmp_rhs65.dtor__1;
        DAST._IType _1770_toType = _let_tmp_rhs65.dtor__2;
        RAST._IType _1771_toTpeGen = _let_tmp_rhs65.dtor__3;
        Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1772_m = _let_tmp_rhs65.dtor__4;
        Dafny.ISequence<Dafny.Rune> _1773_msg;
        _1773_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1769_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1771_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1773_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1765_recursiveGen)._ToString(DCOMP.__default.IND), _1773_msg));
        RAST._IExpr _out282;
        DCOMP._IOwnership _out283;
        (this).FromOwnership(r, _1766_recOwned, expectedOwnership, out _out282, out _out283);
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
      DAST._IExpression _1774_expr = _let_tmp_rhs66.dtor_value;
      DAST._IType _1775_fromTpe = _let_tmp_rhs66.dtor_from;
      DAST._IType _1776_toTpe = _let_tmp_rhs66.dtor_typ;
      if (object.Equals(_1775_fromTpe, _1776_toTpe)) {
        RAST._IExpr _1777_recursiveGen;
        DCOMP._IOwnership _1778_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1779_recIdents;
        RAST._IExpr _out284;
        DCOMP._IOwnership _out285;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out286;
        (this).GenExpr(_1774_expr, selfIdent, env, expectedOwnership, out _out284, out _out285, out _out286);
        _1777_recursiveGen = _out284;
        _1778_recOwned = _out285;
        _1779_recIdents = _out286;
        r = _1777_recursiveGen;
        RAST._IExpr _out287;
        DCOMP._IOwnership _out288;
        (this).FromOwnership(r, _1778_recOwned, expectedOwnership, out _out287, out _out288);
        r = _out287;
        resultingOwnership = _out288;
        readIdents = _1779_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source93 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1775_fromTpe, _1776_toTpe);
        {
          DAST._IType _10 = _source93.dtor__1;
          if (_10.is_UserDefined) {
            DAST._IResolvedType resolved2 = _10.dtor_resolved;
            DAST._IResolvedTypeBase kind2 = resolved2.dtor_kind;
            if (kind2.is_Newtype) {
              DAST._IType _1780_b = kind2.dtor_baseType;
              DAST._INewtypeRange _1781_range = kind2.dtor_range;
              bool _1782_erase = kind2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1783_attributes = resolved2.dtor_attributes;
              {
                RAST._IExpr _out289;
                DCOMP._IOwnership _out290;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out291;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out289, out _out290, out _out291);
                r = _out289;
                resultingOwnership = _out290;
                readIdents = _out291;
              }
              goto after_match39;
            }
          }
        }
        {
          DAST._IType _00 = _source93.dtor__0;
          if (_00.is_UserDefined) {
            DAST._IResolvedType resolved3 = _00.dtor_resolved;
            DAST._IResolvedTypeBase kind3 = resolved3.dtor_kind;
            if (kind3.is_Newtype) {
              DAST._IType _1784_b = kind3.dtor_baseType;
              DAST._INewtypeRange _1785_range = kind3.dtor_range;
              bool _1786_erase = kind3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1787_attributes = resolved3.dtor_attributes;
              {
                RAST._IExpr _out292;
                DCOMP._IOwnership _out293;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out294;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out292, out _out293, out _out294);
                r = _out292;
                resultingOwnership = _out293;
                readIdents = _out294;
              }
              goto after_match39;
            }
          }
        }
        {
          DAST._IType _01 = _source93.dtor__0;
          if (_01.is_Primitive) {
            DAST._IPrimitive _h72 = _01.dtor_Primitive_a0;
            if (_h72.is_Int) {
              DAST._IType _11 = _source93.dtor__1;
              if (_11.is_Primitive) {
                DAST._IPrimitive _h73 = _11.dtor_Primitive_a0;
                if (_h73.is_Real) {
                  {
                    RAST._IExpr _1788_recursiveGen;
                    DCOMP._IOwnership _1789___v137;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1790_recIdents;
                    RAST._IExpr _out295;
                    DCOMP._IOwnership _out296;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out297;
                    (this).GenExpr(_1774_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out295, out _out296, out _out297);
                    _1788_recursiveGen = _out295;
                    _1789___v137 = _out296;
                    _1790_recIdents = _out297;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1788_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out298;
                    DCOMP._IOwnership _out299;
                    (this).FromOwned(r, expectedOwnership, out _out298, out _out299);
                    r = _out298;
                    resultingOwnership = _out299;
                    readIdents = _1790_recIdents;
                  }
                  goto after_match39;
                }
              }
            }
          }
        }
        {
          DAST._IType _02 = _source93.dtor__0;
          if (_02.is_Primitive) {
            DAST._IPrimitive _h74 = _02.dtor_Primitive_a0;
            if (_h74.is_Real) {
              DAST._IType _12 = _source93.dtor__1;
              if (_12.is_Primitive) {
                DAST._IPrimitive _h75 = _12.dtor_Primitive_a0;
                if (_h75.is_Int) {
                  {
                    RAST._IExpr _1791_recursiveGen;
                    DCOMP._IOwnership _1792___v138;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1793_recIdents;
                    RAST._IExpr _out300;
                    DCOMP._IOwnership _out301;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out302;
                    (this).GenExpr(_1774_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out300, out _out301, out _out302);
                    _1791_recursiveGen = _out300;
                    _1792___v138 = _out301;
                    _1793_recIdents = _out302;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1791_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out303;
                    DCOMP._IOwnership _out304;
                    (this).FromOwned(r, expectedOwnership, out _out303, out _out304);
                    r = _out303;
                    resultingOwnership = _out304;
                    readIdents = _1793_recIdents;
                  }
                  goto after_match39;
                }
              }
            }
          }
        }
        {
          DAST._IType _03 = _source93.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h76 = _03.dtor_Primitive_a0;
            if (_h76.is_Int) {
              DAST._IType _13 = _source93.dtor__1;
              if (_13.is_Passthrough) {
                {
                  RAST._IType _1794_rhsType;
                  RAST._IType _out305;
                  _out305 = (this).GenType(_1776_toTpe, DCOMP.GenTypeContext.InBinding());
                  _1794_rhsType = _out305;
                  RAST._IExpr _1795_recursiveGen;
                  DCOMP._IOwnership _1796___v140;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1797_recIdents;
                  RAST._IExpr _out306;
                  DCOMP._IOwnership _out307;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out308;
                  (this).GenExpr(_1774_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out306, out _out307, out _out308);
                  _1795_recursiveGen = _out306;
                  _1796___v140 = _out307;
                  _1797_recIdents = _out308;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1794_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1795_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out309;
                  DCOMP._IOwnership _out310;
                  (this).FromOwned(r, expectedOwnership, out _out309, out _out310);
                  r = _out309;
                  resultingOwnership = _out310;
                  readIdents = _1797_recIdents;
                }
                goto after_match39;
              }
            }
          }
        }
        {
          DAST._IType _04 = _source93.dtor__0;
          if (_04.is_Passthrough) {
            DAST._IType _14 = _source93.dtor__1;
            if (_14.is_Primitive) {
              DAST._IPrimitive _h77 = _14.dtor_Primitive_a0;
              if (_h77.is_Int) {
                {
                  RAST._IType _1798_rhsType;
                  RAST._IType _out311;
                  _out311 = (this).GenType(_1775_fromTpe, DCOMP.GenTypeContext.InBinding());
                  _1798_rhsType = _out311;
                  RAST._IExpr _1799_recursiveGen;
                  DCOMP._IOwnership _1800___v142;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1801_recIdents;
                  RAST._IExpr _out312;
                  DCOMP._IOwnership _out313;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out314;
                  (this).GenExpr(_1774_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out312, out _out313, out _out314);
                  _1799_recursiveGen = _out312;
                  _1800___v142 = _out313;
                  _1801_recIdents = _out314;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_1799_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out315;
                  DCOMP._IOwnership _out316;
                  (this).FromOwned(r, expectedOwnership, out _out315, out _out316);
                  r = _out315;
                  resultingOwnership = _out316;
                  readIdents = _1801_recIdents;
                }
                goto after_match39;
              }
            }
          }
        }
        {
          DAST._IType _05 = _source93.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h78 = _05.dtor_Primitive_a0;
            if (_h78.is_Int) {
              DAST._IType _15 = _source93.dtor__1;
              if (_15.is_Primitive) {
                DAST._IPrimitive _h79 = _15.dtor_Primitive_a0;
                if (_h79.is_Char) {
                  {
                    RAST._IType _1802_rhsType;
                    RAST._IType _out317;
                    _out317 = (this).GenType(_1776_toTpe, DCOMP.GenTypeContext.InBinding());
                    _1802_rhsType = _out317;
                    RAST._IExpr _1803_recursiveGen;
                    DCOMP._IOwnership _1804___v143;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1805_recIdents;
                    RAST._IExpr _out318;
                    DCOMP._IOwnership _out319;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out320;
                    (this).GenExpr(_1774_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out318, out _out319, out _out320);
                    _1803_recursiveGen = _out318;
                    _1804___v143 = _out319;
                    _1805_recIdents = _out320;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1803_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out321;
                    DCOMP._IOwnership _out322;
                    (this).FromOwned(r, expectedOwnership, out _out321, out _out322);
                    r = _out321;
                    resultingOwnership = _out322;
                    readIdents = _1805_recIdents;
                  }
                  goto after_match39;
                }
              }
            }
          }
        }
        {
          DAST._IType _06 = _source93.dtor__0;
          if (_06.is_Primitive) {
            DAST._IPrimitive _h710 = _06.dtor_Primitive_a0;
            if (_h710.is_Char) {
              DAST._IType _16 = _source93.dtor__1;
              if (_16.is_Primitive) {
                DAST._IPrimitive _h711 = _16.dtor_Primitive_a0;
                if (_h711.is_Int) {
                  {
                    RAST._IType _1806_rhsType;
                    RAST._IType _out323;
                    _out323 = (this).GenType(_1775_fromTpe, DCOMP.GenTypeContext.InBinding());
                    _1806_rhsType = _out323;
                    RAST._IExpr _1807_recursiveGen;
                    DCOMP._IOwnership _1808___v144;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1809_recIdents;
                    RAST._IExpr _out324;
                    DCOMP._IOwnership _out325;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out326;
                    (this).GenExpr(_1774_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out324, out _out325, out _out326);
                    _1807_recursiveGen = _out324;
                    _1808___v144 = _out325;
                    _1809_recIdents = _out326;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1807_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out327;
                    DCOMP._IOwnership _out328;
                    (this).FromOwned(r, expectedOwnership, out _out327, out _out328);
                    r = _out327;
                    resultingOwnership = _out328;
                    readIdents = _1809_recIdents;
                  }
                  goto after_match39;
                }
              }
            }
          }
        }
        {
          DAST._IType _07 = _source93.dtor__0;
          if (_07.is_Passthrough) {
            DAST._IType _17 = _source93.dtor__1;
            if (_17.is_Passthrough) {
              {
                RAST._IExpr _1810_recursiveGen;
                DCOMP._IOwnership _1811___v147;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1812_recIdents;
                RAST._IExpr _out329;
                DCOMP._IOwnership _out330;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
                (this).GenExpr(_1774_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out329, out _out330, out _out331);
                _1810_recursiveGen = _out329;
                _1811___v147 = _out330;
                _1812_recIdents = _out331;
                RAST._IType _1813_toTpeGen;
                RAST._IType _out332;
                _out332 = (this).GenType(_1776_toTpe, DCOMP.GenTypeContext.InBinding());
                _1813_toTpeGen = _out332;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1810_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1813_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out333;
                DCOMP._IOwnership _out334;
                (this).FromOwned(r, expectedOwnership, out _out333, out _out334);
                r = _out333;
                resultingOwnership = _out334;
                readIdents = _1812_recIdents;
              }
              goto after_match39;
            }
          }
        }
        {
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
      Std.Wrappers._IOption<RAST._IType> _1814_tpe;
      _1814_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1815_placeboOpt;
      if ((_1814_tpe).is_Some) {
        _1815_placeboOpt = ((_1814_tpe).dtor_value).ExtractMaybePlacebo();
      } else {
        _1815_placeboOpt = Std.Wrappers.Option<RAST._IType>.create_None();
      }
      bool _1816_currentlyBorrowed;
      _1816_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1817_noNeedOfClone;
      _1817_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1815_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _1816_currentlyBorrowed = false;
        _1817_noNeedOfClone = true;
        _1814_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_1815_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        if (_1816_currentlyBorrowed) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        } else {
          resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
        }
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_1814_tpe).is_Some) && (((_1814_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _1818_needObjectFromRef;
        _1818_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source94 = (selfIdent).dtor_dafnyType;
          {
            if (_source94.is_UserDefined) {
              DAST._IResolvedType resolved4 = _source94.dtor_resolved;
              DAST._IResolvedTypeBase _1819_base = resolved4.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _1820_attributes = resolved4.dtor_attributes;
              return ((_1819_base).is_Class) || ((_1819_base).is_Trait);
            }
          }
          {
            return false;
          }
        }))());
        if (_1818_needObjectFromRef) {
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_1817_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1817_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1816_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_1814_tpe).is_Some) && (((_1814_tpe).dtor_value).IsPointer())) {
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
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_1821_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_1821_attributes).UniqueElements, false, (((_exists_var_1) => {
        DAST._IAttribute _1822_attribute = (DAST._IAttribute)_exists_var_1;
        return ((_1821_attributes).Contains(_1822_attribute)) && ((((_1822_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_1822_attribute).dtor_args).Count)) == (new BigInteger(2))));
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
      BigInteger _hi37 = new BigInteger((args).Count);
      for (BigInteger _1823_i = BigInteger.Zero; _1823_i < _hi37; _1823_i++) {
        DCOMP._IOwnership _1824_argOwnership;
        _1824_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if (((name).is_CallName) && ((_1823_i) < (new BigInteger((((name).dtor_signature)).Count)))) {
          RAST._IType _1825_tpe;
          RAST._IType _out338;
          _out338 = (this).GenType(((((name).dtor_signature)).Select(_1823_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _1825_tpe = _out338;
          if ((_1825_tpe).CanReadWithoutClone()) {
            _1824_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _1826_argExpr;
        DCOMP._IOwnership _1827___v154;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1828_argIdents;
        RAST._IExpr _out339;
        DCOMP._IOwnership _out340;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out341;
        (this).GenExpr((args).Select(_1823_i), selfIdent, env, _1824_argOwnership, out _out339, out _out340, out _out341);
        _1826_argExpr = _out339;
        _1827___v154 = _out340;
        _1828_argIdents = _out341;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1826_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1828_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi38 = new BigInteger((typeArgs).Count);
      for (BigInteger _1829_typeI = BigInteger.Zero; _1829_typeI < _hi38; _1829_typeI++) {
        RAST._IType _1830_typeExpr;
        RAST._IType _out342;
        _out342 = (this).GenType((typeArgs).Select(_1829_typeI), DCOMP.GenTypeContext.@default());
        _1830_typeExpr = _out342;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1830_typeExpr));
      }
      DAST._ICallName _source95 = name;
      {
        if (_source95.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _1831_nameIdent = _source95.dtor_name;
          Std.Wrappers._IOption<DAST._IType> onType1 = _source95.dtor_onType;
          if (onType1.is_Some) {
            DAST._IType value10 = onType1.dtor_value;
            if (value10.is_UserDefined) {
              DAST._IResolvedType _1832_resolvedType = value10.dtor_resolved;
              if ((((_1832_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_1833_resolvedType, _1834_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(((_1833_resolvedType).dtor_properMethods).UniqueElements, true, (((_forall_var_8) => {
                Dafny.ISequence<Dafny.Rune> _1835_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_8;
                return !(((_1833_resolvedType).dtor_properMethods).Contains(_1835_m)) || (!object.Equals((_1835_m), _1834_nameIdent));
              }))))(_1832_resolvedType, _1831_nameIdent))) {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_1832_resolvedType, (_1831_nameIdent)), _1832_resolvedType));
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
    public void GenExpr(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source96 = e;
      {
        if (_source96.is_Literal) {
          RAST._IExpr _out343;
          DCOMP._IOwnership _out344;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out345;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out343, out _out344, out _out345);
          r = _out343;
          resultingOwnership = _out344;
          readIdents = _out345;
          goto after_match41;
        }
      }
      {
        if (_source96.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1836_name = _source96.dtor_name;
          {
            RAST._IExpr _out346;
            DCOMP._IOwnership _out347;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out348;
            (this).GenIdent(DCOMP.__default.escapeName(_1836_name), selfIdent, env, expectedOwnership, out _out346, out _out347, out _out348);
            r = _out346;
            resultingOwnership = _out347;
            readIdents = _out348;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1837_path = _source96.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _1838_typeArgs = _source96.dtor_typeArgs;
          {
            RAST._IExpr _out349;
            _out349 = DCOMP.COMP.GenPathExpr(_1837_path);
            r = _out349;
            if ((new BigInteger((_1838_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1839_typeExprs;
              _1839_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi39 = new BigInteger((_1838_typeArgs).Count);
              for (BigInteger _1840_i = BigInteger.Zero; _1840_i < _hi39; _1840_i++) {
                RAST._IType _1841_typeExpr;
                RAST._IType _out350;
                _out350 = (this).GenType((_1838_typeArgs).Select(_1840_i), DCOMP.GenTypeContext.@default());
                _1841_typeExpr = _out350;
                _1839_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1839_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1841_typeExpr));
              }
              r = (r).ApplyType(_1839_typeExprs);
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
          goto after_match41;
        }
      }
      {
        if (_source96.is_InitializationValue) {
          DAST._IType _1842_typ = _source96.dtor_typ;
          {
            RAST._IType _1843_typExpr;
            RAST._IType _out353;
            _out353 = (this).GenType(_1842_typ, DCOMP.GenTypeContext.@default());
            _1843_typExpr = _out353;
            if ((_1843_typExpr).IsObjectOrPointer()) {
              r = (_1843_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1843_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
            }
            RAST._IExpr _out354;
            DCOMP._IOwnership _out355;
            (this).FromOwned(r, expectedOwnership, out _out354, out _out355);
            r = _out354;
            resultingOwnership = _out355;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _1844_values = _source96.dtor_Tuple_a0;
          {
            Dafny.ISequence<RAST._IExpr> _1845_exprs;
            _1845_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi40 = new BigInteger((_1844_values).Count);
            for (BigInteger _1846_i = BigInteger.Zero; _1846_i < _hi40; _1846_i++) {
              RAST._IExpr _1847_recursiveGen;
              DCOMP._IOwnership _1848___v159;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1849_recIdents;
              RAST._IExpr _out356;
              DCOMP._IOwnership _out357;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out358;
              (this).GenExpr((_1844_values).Select(_1846_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out356, out _out357, out _out358);
              _1847_recursiveGen = _out356;
              _1848___v159 = _out357;
              _1849_recIdents = _out358;
              _1845_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1845_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1847_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1849_recIdents);
            }
            if ((new BigInteger((_1844_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) {
              r = RAST.Expr.create_Tuple(_1845_exprs);
            } else {
              r = RAST.__default.SystemTuple(_1845_exprs);
            }
            RAST._IExpr _out359;
            DCOMP._IOwnership _out360;
            (this).FromOwned(r, expectedOwnership, out _out359, out _out360);
            r = _out359;
            resultingOwnership = _out360;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1850_path = _source96.dtor_path;
          Dafny.ISequence<DAST._IType> _1851_typeArgs = _source96.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1852_args = _source96.dtor_args;
          {
            RAST._IExpr _out361;
            _out361 = DCOMP.COMP.GenPathExpr(_1850_path);
            r = _out361;
            if ((new BigInteger((_1851_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1853_typeExprs;
              _1853_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi41 = new BigInteger((_1851_typeArgs).Count);
              for (BigInteger _1854_i = BigInteger.Zero; _1854_i < _hi41; _1854_i++) {
                RAST._IType _1855_typeExpr;
                RAST._IType _out362;
                _out362 = (this).GenType((_1851_typeArgs).Select(_1854_i), DCOMP.GenTypeContext.@default());
                _1855_typeExpr = _out362;
                _1853_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1853_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1855_typeExpr));
              }
              r = (r).ApplyType(_1853_typeExprs);
            }
            r = (r).MSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1856_arguments;
            _1856_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi42 = new BigInteger((_1852_args).Count);
            for (BigInteger _1857_i = BigInteger.Zero; _1857_i < _hi42; _1857_i++) {
              RAST._IExpr _1858_recursiveGen;
              DCOMP._IOwnership _1859___v160;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1860_recIdents;
              RAST._IExpr _out363;
              DCOMP._IOwnership _out364;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out365;
              (this).GenExpr((_1852_args).Select(_1857_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out363, out _out364, out _out365);
              _1858_recursiveGen = _out363;
              _1859___v160 = _out364;
              _1860_recIdents = _out365;
              _1856_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1856_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1858_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1860_recIdents);
            }
            r = (r).Apply(_1856_arguments);
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
        if (_source96.is_NewUninitArray) {
          Dafny.ISequence<DAST._IExpression> _1861_dims = _source96.dtor_dims;
          DAST._IType _1862_typ = _source96.dtor_typ;
          {
            if ((new BigInteger(16)) < (new BigInteger((_1861_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _1863_msg;
              _1863_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1863_msg);
              }
              r = RAST.Expr.create_RawExpr(_1863_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _1864_typeGen;
              RAST._IType _out368;
              _out368 = (this).GenType(_1862_typ, DCOMP.GenTypeContext.@default());
              _1864_typeGen = _out368;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _1865_dimExprs;
              _1865_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi43 = new BigInteger((_1861_dims).Count);
              for (BigInteger _1866_i = BigInteger.Zero; _1866_i < _hi43; _1866_i++) {
                RAST._IExpr _1867_recursiveGen;
                DCOMP._IOwnership _1868___v161;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1869_recIdents;
                RAST._IExpr _out369;
                DCOMP._IOwnership _out370;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out371;
                (this).GenExpr((_1861_dims).Select(_1866_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out369, out _out370, out _out371);
                _1867_recursiveGen = _out369;
                _1868___v161 = _out370;
                _1869_recIdents = _out371;
                _1865_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1865_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.IntoUsize(_1867_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1869_recIdents);
              }
              if ((new BigInteger((_1861_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _1870_class__name;
                _1870_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_1861_dims).Count)));
                r = ((((RAST.__default.dafny__runtime).MSel(_1870_class__name)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1864_typeGen))).MSel((this).placebos__usize)).Apply(_1865_dimExprs);
              } else {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1864_typeGen))).Apply(_1865_dimExprs);
              }
            }
            RAST._IExpr _out372;
            DCOMP._IOwnership _out373;
            (this).FromOwned(r, expectedOwnership, out _out372, out _out373);
            r = _out372;
            resultingOwnership = _out373;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_ArrayIndexToInt) {
          DAST._IExpression _1871_underlying = _source96.dtor_value;
          {
            RAST._IExpr _1872_recursiveGen;
            DCOMP._IOwnership _1873___v162;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1874_recIdents;
            RAST._IExpr _out374;
            DCOMP._IOwnership _out375;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out376;
            (this).GenExpr(_1871_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out374, out _out375, out _out376);
            _1872_recursiveGen = _out374;
            _1873___v162 = _out375;
            _1874_recIdents = _out376;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(_1872_recursiveGen);
            readIdents = _1874_recIdents;
            RAST._IExpr _out377;
            DCOMP._IOwnership _out378;
            (this).FromOwned(r, expectedOwnership, out _out377, out _out378);
            r = _out377;
            resultingOwnership = _out378;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_FinalizeNewArray) {
          DAST._IExpression _1875_underlying = _source96.dtor_value;
          DAST._IType _1876_typ = _source96.dtor_typ;
          {
            RAST._IType _1877_tpe;
            RAST._IType _out379;
            _out379 = (this).GenType(_1876_typ, DCOMP.GenTypeContext.@default());
            _1877_tpe = _out379;
            RAST._IExpr _1878_recursiveGen;
            DCOMP._IOwnership _1879___v163;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1880_recIdents;
            RAST._IExpr _out380;
            DCOMP._IOwnership _out381;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out382;
            (this).GenExpr(_1875_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out380, out _out381, out _out382);
            _1878_recursiveGen = _out380;
            _1879___v163 = _out381;
            _1880_recIdents = _out382;
            readIdents = _1880_recIdents;
            if ((_1877_tpe).IsObjectOrPointer()) {
              RAST._IType _1881_t;
              _1881_t = (_1877_tpe).ObjectOrPointerUnderlying();
              if ((_1881_t).is_Array) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).array__construct)).Apply1(_1878_recursiveGen);
              } else if ((_1881_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _1882_c;
                _1882_c = (_1881_t).MultiArrayClass();
                r = (((RAST.__default.dafny__runtime).MSel(_1882_c)).MSel((this).array__construct)).Apply1(_1878_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_1877_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_1877_tpe)._ToString(DCOMP.__default.IND)));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            }
            RAST._IExpr _out383;
            DCOMP._IOwnership _out384;
            (this).FromOwned(r, expectedOwnership, out _out383, out _out384);
            r = _out383;
            resultingOwnership = _out384;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_DatatypeValue) {
          DAST._IResolvedType _1883_datatypeType = _source96.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1884_typeArgs = _source96.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1885_variant = _source96.dtor_variant;
          bool _1886_isCo = _source96.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1887_values = _source96.dtor_contents;
          {
            RAST._IExpr _out385;
            _out385 = DCOMP.COMP.GenPathExpr((_1883_datatypeType).dtor_path);
            r = _out385;
            Dafny.ISequence<RAST._IType> _1888_genTypeArgs;
            _1888_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi44 = new BigInteger((_1884_typeArgs).Count);
            for (BigInteger _1889_i = BigInteger.Zero; _1889_i < _hi44; _1889_i++) {
              RAST._IType _1890_typeExpr;
              RAST._IType _out386;
              _out386 = (this).GenType((_1884_typeArgs).Select(_1889_i), DCOMP.GenTypeContext.@default());
              _1890_typeExpr = _out386;
              _1888_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1888_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1890_typeExpr));
            }
            if ((new BigInteger((_1884_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1888_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1885_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1891_assignments;
            _1891_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi45 = new BigInteger((_1887_values).Count);
            for (BigInteger _1892_i = BigInteger.Zero; _1892_i < _hi45; _1892_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs67 = (_1887_values).Select(_1892_i);
              Dafny.ISequence<Dafny.Rune> _1893_name = _let_tmp_rhs67.dtor__0;
              DAST._IExpression _1894_value = _let_tmp_rhs67.dtor__1;
              if (_1886_isCo) {
                RAST._IExpr _1895_recursiveGen;
                DCOMP._IOwnership _1896___v164;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1897_recIdents;
                RAST._IExpr _out387;
                DCOMP._IOwnership _out388;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out389;
                (this).GenExpr(_1894_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out387, out _out388, out _out389);
                _1895_recursiveGen = _out387;
                _1896___v164 = _out388;
                _1897_recIdents = _out389;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1897_recIdents);
                Dafny.ISequence<Dafny.Rune> _1898_allReadCloned;
                _1898_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1897_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1899_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1897_recIdents).Elements) {
                    _1899_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1897_recIdents).Contains(_1899_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4437)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1898_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1898_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1899_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1899_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1897_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1897_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1899_next));
                }
                Dafny.ISequence<Dafny.Rune> _1900_wasAssigned;
                _1900_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1898_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1895_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1891_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1891_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1893_name), RAST.Expr.create_RawExpr(_1900_wasAssigned))));
              } else {
                RAST._IExpr _1901_recursiveGen;
                DCOMP._IOwnership _1902___v165;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1903_recIdents;
                RAST._IExpr _out390;
                DCOMP._IOwnership _out391;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out392;
                (this).GenExpr(_1894_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out390, out _out391, out _out392);
                _1901_recursiveGen = _out390;
                _1902___v165 = _out391;
                _1903_recIdents = _out392;
                _1891_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1891_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1893_name), _1901_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1903_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1891_assignments);
            if ((this).IsRcWrapped((_1883_datatypeType).dtor_attributes)) {
              r = RAST.__default.RcNew(r);
            }
            RAST._IExpr _out393;
            DCOMP._IOwnership _out394;
            (this).FromOwned(r, expectedOwnership, out _out393, out _out394);
            r = _out393;
            resultingOwnership = _out394;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_Convert) {
          {
            RAST._IExpr _out395;
            DCOMP._IOwnership _out396;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out397;
            (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out395, out _out396, out _out397);
            r = _out395;
            resultingOwnership = _out396;
            readIdents = _out397;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_SeqConstruct) {
          DAST._IExpression _1904_length = _source96.dtor_length;
          DAST._IExpression _1905_expr = _source96.dtor_elem;
          {
            RAST._IExpr _1906_recursiveGen;
            DCOMP._IOwnership _1907___v169;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1908_recIdents;
            RAST._IExpr _out398;
            DCOMP._IOwnership _out399;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out400;
            (this).GenExpr(_1905_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out398, out _out399, out _out400);
            _1906_recursiveGen = _out398;
            _1907___v169 = _out399;
            _1908_recIdents = _out400;
            RAST._IExpr _1909_lengthGen;
            DCOMP._IOwnership _1910___v170;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1911_lengthIdents;
            RAST._IExpr _out401;
            DCOMP._IOwnership _out402;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
            (this).GenExpr(_1904_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out401, out _out402, out _out403);
            _1909_lengthGen = _out401;
            _1910___v170 = _out402;
            _1911_lengthIdents = _out403;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1906_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1909_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1908_recIdents, _1911_lengthIdents);
            RAST._IExpr _out404;
            DCOMP._IOwnership _out405;
            (this).FromOwned(r, expectedOwnership, out _out404, out _out405);
            r = _out404;
            resultingOwnership = _out405;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _1912_exprs = _source96.dtor_elements;
          DAST._IType _1913_typ = _source96.dtor_typ;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1914_genTpe;
            RAST._IType _out406;
            _out406 = (this).GenType(_1913_typ, DCOMP.GenTypeContext.@default());
            _1914_genTpe = _out406;
            BigInteger _1915_i;
            _1915_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1916_args;
            _1916_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1915_i) < (new BigInteger((_1912_exprs).Count))) {
              RAST._IExpr _1917_recursiveGen;
              DCOMP._IOwnership _1918___v171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1919_recIdents;
              RAST._IExpr _out407;
              DCOMP._IOwnership _out408;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
              (this).GenExpr((_1912_exprs).Select(_1915_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out407, out _out408, out _out409);
              _1917_recursiveGen = _out407;
              _1918___v171 = _out408;
              _1919_recIdents = _out409;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1919_recIdents);
              _1916_args = Dafny.Sequence<RAST._IExpr>.Concat(_1916_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1917_recursiveGen));
              _1915_i = (_1915_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_1916_args);
            if ((new BigInteger((_1916_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1914_genTpe));
            }
            RAST._IExpr _out410;
            DCOMP._IOwnership _out411;
            (this).FromOwned(r, expectedOwnership, out _out410, out _out411);
            r = _out410;
            resultingOwnership = _out411;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _1920_exprs = _source96.dtor_elements;
          {
            Dafny.ISequence<RAST._IExpr> _1921_generatedValues;
            _1921_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1922_i;
            _1922_i = BigInteger.Zero;
            while ((_1922_i) < (new BigInteger((_1920_exprs).Count))) {
              RAST._IExpr _1923_recursiveGen;
              DCOMP._IOwnership _1924___v172;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1925_recIdents;
              RAST._IExpr _out412;
              DCOMP._IOwnership _out413;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out414;
              (this).GenExpr((_1920_exprs).Select(_1922_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out412, out _out413, out _out414);
              _1923_recursiveGen = _out412;
              _1924___v172 = _out413;
              _1925_recIdents = _out414;
              _1921_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1921_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1923_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1925_recIdents);
              _1922_i = (_1922_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_1921_generatedValues);
            RAST._IExpr _out415;
            DCOMP._IOwnership _out416;
            (this).FromOwned(r, expectedOwnership, out _out415, out _out416);
            r = _out415;
            resultingOwnership = _out416;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _1926_exprs = _source96.dtor_elements;
          {
            Dafny.ISequence<RAST._IExpr> _1927_generatedValues;
            _1927_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1928_i;
            _1928_i = BigInteger.Zero;
            while ((_1928_i) < (new BigInteger((_1926_exprs).Count))) {
              RAST._IExpr _1929_recursiveGen;
              DCOMP._IOwnership _1930___v173;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1931_recIdents;
              RAST._IExpr _out417;
              DCOMP._IOwnership _out418;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out419;
              (this).GenExpr((_1926_exprs).Select(_1928_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out417, out _out418, out _out419);
              _1929_recursiveGen = _out417;
              _1930___v173 = _out418;
              _1931_recIdents = _out419;
              _1927_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1927_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1929_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1931_recIdents);
              _1928_i = (_1928_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_1927_generatedValues);
            RAST._IExpr _out420;
            DCOMP._IOwnership _out421;
            (this).FromOwned(r, expectedOwnership, out _out420, out _out421);
            r = _out420;
            resultingOwnership = _out421;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_ToMultiset) {
          DAST._IExpression _1932_expr = _source96.dtor_ToMultiset_a0;
          {
            RAST._IExpr _1933_recursiveGen;
            DCOMP._IOwnership _1934___v174;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1935_recIdents;
            RAST._IExpr _out422;
            DCOMP._IOwnership _out423;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out424;
            (this).GenExpr(_1932_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out422, out _out423, out _out424);
            _1933_recursiveGen = _out422;
            _1934___v174 = _out423;
            _1935_recIdents = _out424;
            r = ((_1933_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _1935_recIdents;
            RAST._IExpr _out425;
            DCOMP._IOwnership _out426;
            (this).FromOwned(r, expectedOwnership, out _out425, out _out426);
            r = _out425;
            resultingOwnership = _out426;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1936_mapElems = _source96.dtor_mapElems;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1937_generatedValues;
            _1937_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1938_i;
            _1938_i = BigInteger.Zero;
            while ((_1938_i) < (new BigInteger((_1936_mapElems).Count))) {
              RAST._IExpr _1939_recursiveGenKey;
              DCOMP._IOwnership _1940___v175;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1941_recIdentsKey;
              RAST._IExpr _out427;
              DCOMP._IOwnership _out428;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out429;
              (this).GenExpr(((_1936_mapElems).Select(_1938_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out427, out _out428, out _out429);
              _1939_recursiveGenKey = _out427;
              _1940___v175 = _out428;
              _1941_recIdentsKey = _out429;
              RAST._IExpr _1942_recursiveGenValue;
              DCOMP._IOwnership _1943___v176;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1944_recIdentsValue;
              RAST._IExpr _out430;
              DCOMP._IOwnership _out431;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out432;
              (this).GenExpr(((_1936_mapElems).Select(_1938_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out430, out _out431, out _out432);
              _1942_recursiveGenValue = _out430;
              _1943___v176 = _out431;
              _1944_recIdentsValue = _out432;
              _1937_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1937_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1939_recursiveGenKey, _1942_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1941_recIdentsKey), _1944_recIdentsValue);
              _1938_i = (_1938_i) + (BigInteger.One);
            }
            _1938_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1945_arguments;
            _1945_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1938_i) < (new BigInteger((_1937_generatedValues).Count))) {
              RAST._IExpr _1946_genKey;
              _1946_genKey = ((_1937_generatedValues).Select(_1938_i)).dtor__0;
              RAST._IExpr _1947_genValue;
              _1947_genValue = ((_1937_generatedValues).Select(_1938_i)).dtor__1;
              _1945_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1945_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1946_genKey, _1947_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _1938_i = (_1938_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_1945_arguments);
            RAST._IExpr _out433;
            DCOMP._IOwnership _out434;
            (this).FromOwned(r, expectedOwnership, out _out433, out _out434);
            r = _out433;
            resultingOwnership = _out434;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_SeqUpdate) {
          DAST._IExpression _1948_expr = _source96.dtor_expr;
          DAST._IExpression _1949_index = _source96.dtor_indexExpr;
          DAST._IExpression _1950_value = _source96.dtor_value;
          {
            RAST._IExpr _1951_exprR;
            DCOMP._IOwnership _1952___v177;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1953_exprIdents;
            RAST._IExpr _out435;
            DCOMP._IOwnership _out436;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out437;
            (this).GenExpr(_1948_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out435, out _out436, out _out437);
            _1951_exprR = _out435;
            _1952___v177 = _out436;
            _1953_exprIdents = _out437;
            RAST._IExpr _1954_indexR;
            DCOMP._IOwnership _1955_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1956_indexIdents;
            RAST._IExpr _out438;
            DCOMP._IOwnership _out439;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out440;
            (this).GenExpr(_1949_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out438, out _out439, out _out440);
            _1954_indexR = _out438;
            _1955_indexOwnership = _out439;
            _1956_indexIdents = _out440;
            RAST._IExpr _1957_valueR;
            DCOMP._IOwnership _1958_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1959_valueIdents;
            RAST._IExpr _out441;
            DCOMP._IOwnership _out442;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out443;
            (this).GenExpr(_1950_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out441, out _out442, out _out443);
            _1957_valueR = _out441;
            _1958_valueOwnership = _out442;
            _1959_valueIdents = _out443;
            r = ((_1951_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1954_indexR, _1957_valueR));
            RAST._IExpr _out444;
            DCOMP._IOwnership _out445;
            (this).FromOwned(r, expectedOwnership, out _out444, out _out445);
            r = _out444;
            resultingOwnership = _out445;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1953_exprIdents, _1956_indexIdents), _1959_valueIdents);
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_MapUpdate) {
          DAST._IExpression _1960_expr = _source96.dtor_expr;
          DAST._IExpression _1961_index = _source96.dtor_indexExpr;
          DAST._IExpression _1962_value = _source96.dtor_value;
          {
            RAST._IExpr _1963_exprR;
            DCOMP._IOwnership _1964___v178;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1965_exprIdents;
            RAST._IExpr _out446;
            DCOMP._IOwnership _out447;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out448;
            (this).GenExpr(_1960_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out446, out _out447, out _out448);
            _1963_exprR = _out446;
            _1964___v178 = _out447;
            _1965_exprIdents = _out448;
            RAST._IExpr _1966_indexR;
            DCOMP._IOwnership _1967_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1968_indexIdents;
            RAST._IExpr _out449;
            DCOMP._IOwnership _out450;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
            (this).GenExpr(_1961_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out449, out _out450, out _out451);
            _1966_indexR = _out449;
            _1967_indexOwnership = _out450;
            _1968_indexIdents = _out451;
            RAST._IExpr _1969_valueR;
            DCOMP._IOwnership _1970_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1971_valueIdents;
            RAST._IExpr _out452;
            DCOMP._IOwnership _out453;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out454;
            (this).GenExpr(_1962_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out452, out _out453, out _out454);
            _1969_valueR = _out452;
            _1970_valueOwnership = _out453;
            _1971_valueIdents = _out454;
            r = ((_1963_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1966_indexR, _1969_valueR));
            RAST._IExpr _out455;
            DCOMP._IOwnership _out456;
            (this).FromOwned(r, expectedOwnership, out _out455, out _out456);
            r = _out455;
            resultingOwnership = _out456;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1965_exprIdents, _1968_indexIdents), _1971_valueIdents);
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_This) {
          {
            DCOMP._ISelfInfo _source97 = selfIdent;
            {
              if (_source97.is_ThisTyped) {
                Dafny.ISequence<Dafny.Rune> _1972_id = _source97.dtor_rSelfName;
                DAST._IType _1973_dafnyType = _source97.dtor_dafnyType;
                {
                  RAST._IExpr _out457;
                  DCOMP._IOwnership _out458;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out459;
                  (this).GenIdent(_1972_id, selfIdent, env, expectedOwnership, out _out457, out _out458, out _out459);
                  r = _out457;
                  resultingOwnership = _out458;
                  readIdents = _out459;
                }
                goto after_match42;
              }
            }
            {
              DCOMP._ISelfInfo _1974_None = _source97;
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
          after_match42: ;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_Ite) {
          DAST._IExpression _1975_cond = _source96.dtor_cond;
          DAST._IExpression _1976_t = _source96.dtor_thn;
          DAST._IExpression _1977_f = _source96.dtor_els;
          {
            RAST._IExpr _1978_cond;
            DCOMP._IOwnership _1979___v179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1980_recIdentsCond;
            RAST._IExpr _out462;
            DCOMP._IOwnership _out463;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out464;
            (this).GenExpr(_1975_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out462, out _out463, out _out464);
            _1978_cond = _out462;
            _1979___v179 = _out463;
            _1980_recIdentsCond = _out464;
            RAST._IExpr _1981_fExpr;
            DCOMP._IOwnership _1982_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1983_recIdentsF;
            RAST._IExpr _out465;
            DCOMP._IOwnership _out466;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out467;
            (this).GenExpr(_1977_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out465, out _out466, out _out467);
            _1981_fExpr = _out465;
            _1982_fOwned = _out466;
            _1983_recIdentsF = _out467;
            RAST._IExpr _1984_tExpr;
            DCOMP._IOwnership _1985___v180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1986_recIdentsT;
            RAST._IExpr _out468;
            DCOMP._IOwnership _out469;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out470;
            (this).GenExpr(_1976_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out468, out _out469, out _out470);
            _1984_tExpr = _out468;
            _1985___v180 = _out469;
            _1986_recIdentsT = _out470;
            r = RAST.Expr.create_IfExpr(_1978_cond, _1984_tExpr, _1981_fExpr);
            RAST._IExpr _out471;
            DCOMP._IOwnership _out472;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out471, out _out472);
            r = _out471;
            resultingOwnership = _out472;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1980_recIdentsCond, _1986_recIdentsT), _1983_recIdentsF);
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source96.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _1987_e = _source96.dtor_expr;
            DAST.Format._IUnaryOpFormat _1988_format = _source96.dtor_format1;
            {
              RAST._IExpr _1989_recursiveGen;
              DCOMP._IOwnership _1990___v181;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1991_recIdents;
              RAST._IExpr _out473;
              DCOMP._IOwnership _out474;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out475;
              (this).GenExpr(_1987_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out473, out _out474, out _out475);
              _1989_recursiveGen = _out473;
              _1990___v181 = _out474;
              _1991_recIdents = _out475;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _1989_recursiveGen, _1988_format);
              RAST._IExpr _out476;
              DCOMP._IOwnership _out477;
              (this).FromOwned(r, expectedOwnership, out _out476, out _out477);
              r = _out476;
              resultingOwnership = _out477;
              readIdents = _1991_recIdents;
              return ;
            }
            goto after_match41;
          }
        }
      }
      {
        if (_source96.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source96.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _1992_e = _source96.dtor_expr;
            DAST.Format._IUnaryOpFormat _1993_format = _source96.dtor_format1;
            {
              RAST._IExpr _1994_recursiveGen;
              DCOMP._IOwnership _1995___v182;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1996_recIdents;
              RAST._IExpr _out478;
              DCOMP._IOwnership _out479;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out480;
              (this).GenExpr(_1992_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out478, out _out479, out _out480);
              _1994_recursiveGen = _out478;
              _1995___v182 = _out479;
              _1996_recIdents = _out480;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _1994_recursiveGen, _1993_format);
              RAST._IExpr _out481;
              DCOMP._IOwnership _out482;
              (this).FromOwned(r, expectedOwnership, out _out481, out _out482);
              r = _out481;
              resultingOwnership = _out482;
              readIdents = _1996_recIdents;
              return ;
            }
            goto after_match41;
          }
        }
      }
      {
        if (_source96.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source96.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _1997_e = _source96.dtor_expr;
            DAST.Format._IUnaryOpFormat _1998_format = _source96.dtor_format1;
            {
              RAST._IExpr _1999_recursiveGen;
              DCOMP._IOwnership _2000_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2001_recIdents;
              RAST._IExpr _out483;
              DCOMP._IOwnership _out484;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out485;
              (this).GenExpr(_1997_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out483, out _out484, out _out485);
              _1999_recursiveGen = _out483;
              _2000_recOwned = _out484;
              _2001_recIdents = _out485;
              r = ((_1999_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out486;
              DCOMP._IOwnership _out487;
              (this).FromOwned(r, expectedOwnership, out _out486, out _out487);
              r = _out486;
              resultingOwnership = _out487;
              readIdents = _2001_recIdents;
              return ;
            }
            goto after_match41;
          }
        }
      }
      {
        if (_source96.is_BinOp) {
          RAST._IExpr _out488;
          DCOMP._IOwnership _out489;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out490;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out488, out _out489, out _out490);
          r = _out488;
          resultingOwnership = _out489;
          readIdents = _out490;
          goto after_match41;
        }
      }
      {
        if (_source96.is_ArrayLen) {
          DAST._IExpression _2002_expr = _source96.dtor_expr;
          DAST._IType _2003_exprType = _source96.dtor_exprType;
          BigInteger _2004_dim = _source96.dtor_dim;
          bool _2005_native = _source96.dtor_native;
          {
            RAST._IExpr _2006_recursiveGen;
            DCOMP._IOwnership _2007___v187;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2008_recIdents;
            RAST._IExpr _out491;
            DCOMP._IOwnership _out492;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out493;
            (this).GenExpr(_2002_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out491, out _out492, out _out493);
            _2006_recursiveGen = _out491;
            _2007___v187 = _out492;
            _2008_recIdents = _out493;
            RAST._IType _2009_arrayType;
            RAST._IType _out494;
            _out494 = (this).GenType(_2003_exprType, DCOMP.GenTypeContext.@default());
            _2009_arrayType = _out494;
            if (!((_2009_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _2010_msg;
              _2010_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_2009_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2010_msg);
              r = RAST.Expr.create_RawExpr(_2010_msg);
            } else {
              RAST._IType _2011_underlying;
              _2011_underlying = (_2009_arrayType).ObjectOrPointerUnderlying();
              if (((_2004_dim).Sign == 0) && ((_2011_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_2006_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_2004_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_2006_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = ((((this).read__macro).Apply1(_2006_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("length"), Std.Strings.__default.OfNat(_2004_dim)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_usize")))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                }
              }
              if (!(_2005_native)) {
                r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(r);
              }
            }
            RAST._IExpr _out495;
            DCOMP._IOwnership _out496;
            (this).FromOwned(r, expectedOwnership, out _out495, out _out496);
            r = _out495;
            resultingOwnership = _out496;
            readIdents = _2008_recIdents;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_MapKeys) {
          DAST._IExpression _2012_expr = _source96.dtor_expr;
          {
            RAST._IExpr _2013_recursiveGen;
            DCOMP._IOwnership _2014___v188;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2015_recIdents;
            RAST._IExpr _out497;
            DCOMP._IOwnership _out498;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out499;
            (this).GenExpr(_2012_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out497, out _out498, out _out499);
            _2013_recursiveGen = _out497;
            _2014___v188 = _out498;
            _2015_recIdents = _out499;
            readIdents = _2015_recIdents;
            r = ((_2013_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out500;
            DCOMP._IOwnership _out501;
            (this).FromOwned(r, expectedOwnership, out _out500, out _out501);
            r = _out500;
            resultingOwnership = _out501;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_MapValues) {
          DAST._IExpression _2016_expr = _source96.dtor_expr;
          {
            RAST._IExpr _2017_recursiveGen;
            DCOMP._IOwnership _2018___v189;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2019_recIdents;
            RAST._IExpr _out502;
            DCOMP._IOwnership _out503;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out504;
            (this).GenExpr(_2016_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out502, out _out503, out _out504);
            _2017_recursiveGen = _out502;
            _2018___v189 = _out503;
            _2019_recIdents = _out504;
            readIdents = _2019_recIdents;
            r = ((_2017_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out505;
            DCOMP._IOwnership _out506;
            (this).FromOwned(r, expectedOwnership, out _out505, out _out506);
            r = _out505;
            resultingOwnership = _out506;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_SelectFn) {
          DAST._IExpression _2020_on = _source96.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2021_field = _source96.dtor_field;
          bool _2022_isDatatype = _source96.dtor_onDatatype;
          bool _2023_isStatic = _source96.dtor_isStatic;
          BigInteger _2024_arity = _source96.dtor_arity;
          {
            RAST._IExpr _2025_onExpr;
            DCOMP._IOwnership _2026_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2027_recIdents;
            RAST._IExpr _out507;
            DCOMP._IOwnership _out508;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out509;
            (this).GenExpr(_2020_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out507, out _out508, out _out509);
            _2025_onExpr = _out507;
            _2026_onOwned = _out508;
            _2027_recIdents = _out509;
            Dafny.ISequence<Dafny.Rune> _2028_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _2029_onString;
            _2029_onString = (_2025_onExpr)._ToString(DCOMP.__default.IND);
            if (_2023_isStatic) {
              _2028_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2029_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_2021_field));
            } else {
              _2028_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _2028_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2028_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2029_onString), ((object.Equals(_2026_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _2030_args;
              _2030_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _2031_i;
              _2031_i = BigInteger.Zero;
              while ((_2031_i) < (_2024_arity)) {
                if ((_2031_i).Sign == 1) {
                  _2030_args = Dafny.Sequence<Dafny.Rune>.Concat(_2030_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _2030_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2030_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_2031_i));
                _2031_i = (_2031_i) + (BigInteger.One);
              }
              _2028_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2028_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2030_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _2028_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2028_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_2021_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2030_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _2028_s = Dafny.Sequence<Dafny.Rune>.Concat(_2028_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _2028_s = Dafny.Sequence<Dafny.Rune>.Concat(_2028_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _2032_typeShape;
            _2032_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _2033_i;
            _2033_i = BigInteger.Zero;
            while ((_2033_i) < (_2024_arity)) {
              if ((_2033_i).Sign == 1) {
                _2032_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2032_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2032_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2032_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _2033_i = (_2033_i) + (BigInteger.One);
            }
            _2032_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2032_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _2028_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _2028_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _2032_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_2028_s);
            RAST._IExpr _out510;
            DCOMP._IOwnership _out511;
            (this).FromOwned(r, expectedOwnership, out _out510, out _out511);
            r = _out510;
            resultingOwnership = _out511;
            readIdents = _2027_recIdents;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_Select) {
          DAST._IExpression expr0 = _source96.dtor_expr;
          if (expr0.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2034_c = expr0.dtor_Companion_a0;
            Dafny.ISequence<DAST._IType> _2035_typeArgs = expr0.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _2036_field = _source96.dtor_field;
            bool _2037_isConstant = _source96.dtor_isConstant;
            bool _2038_isDatatype = _source96.dtor_onDatatype;
            DAST._IType _2039_fieldType = _source96.dtor_fieldType;
            {
              RAST._IExpr _2040_onExpr;
              DCOMP._IOwnership _2041_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2042_recIdents;
              RAST._IExpr _out512;
              DCOMP._IOwnership _out513;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out514;
              (this).GenExpr(DAST.Expression.create_Companion(_2034_c, _2035_typeArgs), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out512, out _out513, out _out514);
              _2040_onExpr = _out512;
              _2041_onOwned = _out513;
              _2042_recIdents = _out514;
              r = ((_2040_onExpr).MSel(DCOMP.__default.escapeName(_2036_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out515;
              DCOMP._IOwnership _out516;
              (this).FromOwned(r, expectedOwnership, out _out515, out _out516);
              r = _out515;
              resultingOwnership = _out516;
              readIdents = _2042_recIdents;
              return ;
            }
            goto after_match41;
          }
        }
      }
      {
        if (_source96.is_Select) {
          DAST._IExpression _2043_on = _source96.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2044_field = _source96.dtor_field;
          bool _2045_isConstant = _source96.dtor_isConstant;
          bool _2046_isDatatype = _source96.dtor_onDatatype;
          DAST._IType _2047_fieldType = _source96.dtor_fieldType;
          {
            if (_2046_isDatatype) {
              RAST._IExpr _2048_onExpr;
              DCOMP._IOwnership _2049_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2050_recIdents;
              RAST._IExpr _out517;
              DCOMP._IOwnership _out518;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out519;
              (this).GenExpr(_2043_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out517, out _out518, out _out519);
              _2048_onExpr = _out517;
              _2049_onOwned = _out518;
              _2050_recIdents = _out519;
              r = ((_2048_onExpr).Sel(DCOMP.__default.escapeName(_2044_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _2051_typ;
              RAST._IType _out520;
              _out520 = (this).GenType(_2047_fieldType, DCOMP.GenTypeContext.@default());
              _2051_typ = _out520;
              RAST._IExpr _out521;
              DCOMP._IOwnership _out522;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out521, out _out522);
              r = _out521;
              resultingOwnership = _out522;
              readIdents = _2050_recIdents;
            } else {
              RAST._IExpr _2052_onExpr;
              DCOMP._IOwnership _2053_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2054_recIdents;
              RAST._IExpr _out523;
              DCOMP._IOwnership _out524;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
              (this).GenExpr(_2043_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out523, out _out524, out _out525);
              _2052_onExpr = _out523;
              _2053_onOwned = _out524;
              _2054_recIdents = _out525;
              r = _2052_onExpr;
              if (!object.Equals(_2052_onExpr, RAST.__default.self)) {
                RAST._IExpr _source98 = _2052_onExpr;
                {
                  if (_source98.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> op15 = _source98.dtor_op1;
                    if (object.Equals(op15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                      RAST._IExpr underlying5 = _source98.dtor_underlying;
                      if (underlying5.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name15 = underlying5.dtor_name;
                        if (object.Equals(name15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
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
              r = (r).Sel(DCOMP.__default.escapeName(_2044_field));
              if (_2045_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out526;
              DCOMP._IOwnership _out527;
              (this).FromOwned(r, expectedOwnership, out _out526, out _out527);
              r = _out526;
              resultingOwnership = _out527;
              readIdents = _2054_recIdents;
            }
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_Index) {
          DAST._IExpression _2055_on = _source96.dtor_expr;
          DAST._ICollKind _2056_collKind = _source96.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2057_indices = _source96.dtor_indices;
          {
            RAST._IExpr _2058_onExpr;
            DCOMP._IOwnership _2059_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2060_recIdents;
            RAST._IExpr _out528;
            DCOMP._IOwnership _out529;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out530;
            (this).GenExpr(_2055_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out528, out _out529, out _out530);
            _2058_onExpr = _out528;
            _2059_onOwned = _out529;
            _2060_recIdents = _out530;
            readIdents = _2060_recIdents;
            r = _2058_onExpr;
            bool _2061_hadArray;
            _2061_hadArray = false;
            if (object.Equals(_2056_collKind, DAST.CollKind.create_Array())) {
              r = ((this).read__macro).Apply1(r);
              _2061_hadArray = true;
              if ((new BigInteger((_2057_indices).Count)) > (BigInteger.One)) {
                r = (r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
              }
            }
            BigInteger _hi46 = new BigInteger((_2057_indices).Count);
            for (BigInteger _2062_i = BigInteger.Zero; _2062_i < _hi46; _2062_i++) {
              if (object.Equals(_2056_collKind, DAST.CollKind.create_Array())) {
                RAST._IExpr _2063_idx;
                DCOMP._IOwnership _2064_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2065_recIdentsIdx;
                RAST._IExpr _out531;
                DCOMP._IOwnership _out532;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out533;
                (this).GenExpr((_2057_indices).Select(_2062_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out531, out _out532, out _out533);
                _2063_idx = _out531;
                _2064_idxOwned = _out532;
                _2065_recIdentsIdx = _out533;
                _2063_idx = RAST.__default.IntoUsize(_2063_idx);
                r = RAST.Expr.create_SelectIndex(r, _2063_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2065_recIdentsIdx);
              } else {
                RAST._IExpr _2066_idx;
                DCOMP._IOwnership _2067_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2068_recIdentsIdx;
                RAST._IExpr _out534;
                DCOMP._IOwnership _out535;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out536;
                (this).GenExpr((_2057_indices).Select(_2062_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out534, out _out535, out _out536);
                _2066_idx = _out534;
                _2067_idxOwned = _out535;
                _2068_recIdentsIdx = _out536;
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_2066_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2068_recIdentsIdx);
              }
            }
            if (_2061_hadArray) {
              r = (r).Clone();
            }
            RAST._IExpr _out537;
            DCOMP._IOwnership _out538;
            (this).FromOwned(r, expectedOwnership, out _out537, out _out538);
            r = _out537;
            resultingOwnership = _out538;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_IndexRange) {
          DAST._IExpression _2069_on = _source96.dtor_expr;
          bool _2070_isArray = _source96.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _2071_low = _source96.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _2072_high = _source96.dtor_high;
          {
            RAST._IExpr _2073_onExpr;
            DCOMP._IOwnership _2074_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2075_recIdents;
            RAST._IExpr _out539;
            DCOMP._IOwnership _out540;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
            (this).GenExpr(_2069_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out539, out _out540, out _out541);
            _2073_onExpr = _out539;
            _2074_onOwned = _out540;
            _2075_recIdents = _out541;
            readIdents = _2075_recIdents;
            Dafny.ISequence<Dafny.Rune> _2076_methodName;
            if ((_2071_low).is_Some) {
              if ((_2072_high).is_Some) {
                _2076_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice");
              } else {
                _2076_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop");
              }
            } else if ((_2072_high).is_Some) {
              _2076_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take");
            } else {
              _2076_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            }
            Dafny.ISequence<RAST._IExpr> _2077_arguments;
            _2077_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source99 = _2071_low;
            {
              if (_source99.is_Some) {
                DAST._IExpression _2078_l = _source99.dtor_value;
                {
                  RAST._IExpr _2079_lExpr;
                  DCOMP._IOwnership _2080___v192;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2081_recIdentsL;
                  RAST._IExpr _out542;
                  DCOMP._IOwnership _out543;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out544;
                  (this).GenExpr(_2078_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out542, out _out543, out _out544);
                  _2079_lExpr = _out542;
                  _2080___v192 = _out543;
                  _2081_recIdentsL = _out544;
                  _2077_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2077_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2079_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2081_recIdentsL);
                }
                goto after_match44;
              }
            }
            {
            }
          after_match44: ;
            Std.Wrappers._IOption<DAST._IExpression> _source100 = _2072_high;
            {
              if (_source100.is_Some) {
                DAST._IExpression _2082_h = _source100.dtor_value;
                {
                  RAST._IExpr _2083_hExpr;
                  DCOMP._IOwnership _2084___v193;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2085_recIdentsH;
                  RAST._IExpr _out545;
                  DCOMP._IOwnership _out546;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out547;
                  (this).GenExpr(_2082_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out545, out _out546, out _out547);
                  _2083_hExpr = _out545;
                  _2084___v193 = _out546;
                  _2085_recIdentsH = _out547;
                  _2077_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2077_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2083_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2085_recIdentsH);
                }
                goto after_match45;
              }
            }
            {
            }
          after_match45: ;
            r = _2073_onExpr;
            if (_2070_isArray) {
              if (!(_2076_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _2076_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2076_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _2076_methodName))).Apply(_2077_arguments);
            } else {
              if (!(_2076_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_2076_methodName)).Apply(_2077_arguments);
              }
            }
            RAST._IExpr _out548;
            DCOMP._IOwnership _out549;
            (this).FromOwned(r, expectedOwnership, out _out548, out _out549);
            r = _out548;
            resultingOwnership = _out549;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_TupleSelect) {
          DAST._IExpression _2086_on = _source96.dtor_expr;
          BigInteger _2087_idx = _source96.dtor_index;
          DAST._IType _2088_fieldType = _source96.dtor_fieldType;
          {
            RAST._IExpr _2089_onExpr;
            DCOMP._IOwnership _2090_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2091_recIdents;
            RAST._IExpr _out550;
            DCOMP._IOwnership _out551;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out552;
            (this).GenExpr(_2086_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out550, out _out551, out _out552);
            _2089_onExpr = _out550;
            _2090_onOwnership = _out551;
            _2091_recIdents = _out552;
            Dafny.ISequence<Dafny.Rune> _2092_selName;
            _2092_selName = Std.Strings.__default.OfNat(_2087_idx);
            DAST._IType _source101 = _2088_fieldType;
            {
              if (_source101.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2093_tps = _source101.dtor_Tuple_a0;
                if (((_2088_fieldType).is_Tuple) && ((new BigInteger((_2093_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _2092_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2092_selName);
                }
                goto after_match46;
              }
            }
            {
            }
          after_match46: ;
            r = ((_2089_onExpr).Sel(_2092_selName)).Clone();
            RAST._IExpr _out553;
            DCOMP._IOwnership _out554;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out553, out _out554);
            r = _out553;
            resultingOwnership = _out554;
            readIdents = _2091_recIdents;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_Call) {
          DAST._IExpression _2094_on = _source96.dtor_on;
          DAST._ICallName _2095_name = _source96.dtor_callName;
          Dafny.ISequence<DAST._IType> _2096_typeArgs = _source96.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2097_args = _source96.dtor_args;
          {
            Dafny.ISequence<RAST._IExpr> _2098_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2099_recIdents;
            Dafny.ISequence<RAST._IType> _2100_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _2101_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out555;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out556;
            Dafny.ISequence<RAST._IType> _out557;
            Std.Wrappers._IOption<DAST._IResolvedType> _out558;
            (this).GenArgs(selfIdent, _2095_name, _2096_typeArgs, _2097_args, env, out _out555, out _out556, out _out557, out _out558);
            _2098_argExprs = _out555;
            _2099_recIdents = _out556;
            _2100_typeExprs = _out557;
            _2101_fullNameQualifier = _out558;
            readIdents = _2099_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source102 = _2101_fullNameQualifier;
            {
              if (_source102.is_Some) {
                DAST._IResolvedType value11 = _source102.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2102_path = value11.dtor_path;
                Dafny.ISequence<DAST._IType> _2103_onTypeArgs = value11.dtor_typeArgs;
                DAST._IResolvedTypeBase _2104_base = value11.dtor_kind;
                RAST._IExpr _2105_fullPath;
                RAST._IExpr _out559;
                _out559 = DCOMP.COMP.GenPathExpr(_2102_path);
                _2105_fullPath = _out559;
                Dafny.ISequence<RAST._IType> _2106_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out560;
                _out560 = (this).GenTypeArgs(_2103_onTypeArgs, DCOMP.GenTypeContext.@default());
                _2106_onTypeExprs = _out560;
                RAST._IExpr _2107_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _2108_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2109_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_2104_base).is_Trait) || ((_2104_base).is_Class)) {
                  RAST._IExpr _out561;
                  DCOMP._IOwnership _out562;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out563;
                  (this).GenExpr(_2094_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out561, out _out562, out _out563);
                  _2107_onExpr = _out561;
                  _2108_recOwnership = _out562;
                  _2109_recIdents = _out563;
                  _2107_onExpr = ((this).read__macro).Apply1(_2107_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2109_recIdents);
                } else {
                  RAST._IExpr _out564;
                  DCOMP._IOwnership _out565;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out566;
                  (this).GenExpr(_2094_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out564, out _out565, out _out566);
                  _2107_onExpr = _out564;
                  _2108_recOwnership = _out565;
                  _2109_recIdents = _out566;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2109_recIdents);
                }
                r = ((((_2105_fullPath).ApplyType(_2106_onTypeExprs)).MSel(DCOMP.__default.escapeName((_2095_name).dtor_name))).ApplyType(_2100_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_2107_onExpr), _2098_argExprs));
                RAST._IExpr _out567;
                DCOMP._IOwnership _out568;
                (this).FromOwned(r, expectedOwnership, out _out567, out _out568);
                r = _out567;
                resultingOwnership = _out568;
                goto after_match47;
              }
            }
            {
              RAST._IExpr _2110_onExpr;
              DCOMP._IOwnership _2111___v199;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2112_recIdents;
              RAST._IExpr _out569;
              DCOMP._IOwnership _out570;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out571;
              (this).GenExpr(_2094_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out569, out _out570, out _out571);
              _2110_onExpr = _out569;
              _2111___v199 = _out570;
              _2112_recIdents = _out571;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2112_recIdents);
              Dafny.ISequence<Dafny.Rune> _2113_renderedName;
              DAST._ICallName _source103 = _2095_name;
              {
                if (_source103.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _2114_ident = _source103.dtor_name;
                  _2113_renderedName = DCOMP.__default.escapeName(_2114_ident);
                  goto after_match48;
                }
              }
              {
                bool disjunctiveMatch13 = false;
                if (_source103.is_MapBuilderAdd) {
                  disjunctiveMatch13 = true;
                }
                if (_source103.is_SetBuilderAdd) {
                  disjunctiveMatch13 = true;
                }
                if (disjunctiveMatch13) {
                  _2113_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                  goto after_match48;
                }
              }
              {
                _2113_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
              }
            after_match48: ;
              DAST._IExpression _source104 = _2094_on;
              {
                if (_source104.is_Companion) {
                  {
                    _2110_onExpr = (_2110_onExpr).MSel(_2113_renderedName);
                  }
                  goto after_match49;
                }
              }
              {
                {
                  if (!object.Equals(_2110_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source105 = _2095_name;
                    {
                      if (_source105.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType2 = _source105.dtor_onType;
                        if (onType2.is_Some) {
                          DAST._IType _2115_tpe = onType2.dtor_value;
                          RAST._IType _2116_typ;
                          RAST._IType _out572;
                          _out572 = (this).GenType(_2115_tpe, DCOMP.GenTypeContext.@default());
                          _2116_typ = _out572;
                          if ((_2116_typ).IsObjectOrPointer()) {
                            _2110_onExpr = ((this).read__macro).Apply1(_2110_onExpr);
                          }
                          goto after_match50;
                        }
                      }
                    }
                    {
                    }
                  after_match50: ;
                  }
                  _2110_onExpr = (_2110_onExpr).Sel(_2113_renderedName);
                }
              }
            after_match49: ;
              r = ((_2110_onExpr).ApplyType(_2100_typeExprs)).Apply(_2098_argExprs);
              RAST._IExpr _out573;
              DCOMP._IOwnership _out574;
              (this).FromOwned(r, expectedOwnership, out _out573, out _out574);
              r = _out573;
              resultingOwnership = _out574;
              return ;
            }
          after_match47: ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2117_paramsDafny = _source96.dtor_params;
          DAST._IType _2118_retType = _source96.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2119_body = _source96.dtor_body;
          {
            Dafny.ISequence<RAST._IFormal> _2120_params;
            Dafny.ISequence<RAST._IFormal> _out575;
            _out575 = (this).GenParams(_2117_paramsDafny);
            _2120_params = _out575;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2121_paramNames;
            _2121_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2122_paramTypesMap;
            _2122_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi47 = new BigInteger((_2120_params).Count);
            for (BigInteger _2123_i = BigInteger.Zero; _2123_i < _hi47; _2123_i++) {
              Dafny.ISequence<Dafny.Rune> _2124_name;
              _2124_name = ((_2120_params).Select(_2123_i)).dtor_name;
              _2121_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2121_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2124_name));
              _2122_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2122_paramTypesMap, _2124_name, ((_2120_params).Select(_2123_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _2125_subEnv;
            _2125_subEnv = ((env).ToOwned()).merge(DCOMP.Environment.create(_2121_paramNames, _2122_paramTypesMap));
            RAST._IExpr _2126_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2127_recIdents;
            DCOMP._IEnvironment _2128___v210;
            RAST._IExpr _out576;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out577;
            DCOMP._IEnvironment _out578;
            (this).GenStmts(_2119_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _2125_subEnv, true, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out576, out _out577, out _out578);
            _2126_recursiveGen = _out576;
            _2127_recIdents = _out577;
            _2128___v210 = _out578;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _2127_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2127_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_2129_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll7 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_7 in (_2129_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _2130_name = (Dafny.ISequence<Dafny.Rune>)_compr_7;
                if ((_2129_paramNames).Contains(_2130_name)) {
                  _coll7.Add(_2130_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll7);
            }))())(_2121_paramNames));
            RAST._IExpr _2131_allReadCloned;
            _2131_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_2127_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _2132_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_2127_recIdents).Elements) {
                _2132_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_2127_recIdents).Contains(_2132_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 4912)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_2132_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _2133_selfCloned;
                DCOMP._IOwnership _2134___v211;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2135___v212;
                RAST._IExpr _out579;
                DCOMP._IOwnership _out580;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out581;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out579, out _out580, out _out581);
                _2133_selfCloned = _out579;
                _2134___v211 = _out580;
                _2135___v212 = _out581;
                _2131_allReadCloned = (_2131_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2133_selfCloned)));
              } else if (!((_2121_paramNames).Contains(_2132_next))) {
                RAST._IExpr _2136_copy;
                _2136_copy = (RAST.Expr.create_Identifier(_2132_next)).Clone();
                _2131_allReadCloned = (_2131_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2132_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2136_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2132_next));
              }
              _2127_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2127_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2132_next));
            }
            RAST._IType _2137_retTypeGen;
            RAST._IType _out582;
            _out582 = (this).GenType(_2118_retType, DCOMP.GenTypeContext.InFn());
            _2137_retTypeGen = _out582;
            r = RAST.Expr.create_Block((_2131_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_2120_params, Std.Wrappers.Option<RAST._IType>.create_Some(_2137_retTypeGen), RAST.Expr.create_Block(_2126_recursiveGen)))));
            RAST._IExpr _out583;
            DCOMP._IOwnership _out584;
            (this).FromOwned(r, expectedOwnership, out _out583, out _out584);
            r = _out583;
            resultingOwnership = _out584;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2138_values = _source96.dtor_values;
          DAST._IType _2139_retType = _source96.dtor_retType;
          DAST._IExpression _2140_expr = _source96.dtor_expr;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2141_paramNames;
            _2141_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2142_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out585;
            _out585 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2143_value) => {
              return (_2143_value).dtor__0;
            })), _2138_values));
            _2142_paramFormals = _out585;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2144_paramTypes;
            _2144_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2145_paramNamesSet;
            _2145_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi48 = new BigInteger((_2138_values).Count);
            for (BigInteger _2146_i = BigInteger.Zero; _2146_i < _hi48; _2146_i++) {
              Dafny.ISequence<Dafny.Rune> _2147_name;
              _2147_name = (((_2138_values).Select(_2146_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2148_rName;
              _2148_rName = DCOMP.__default.escapeName(_2147_name);
              _2141_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2141_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2148_rName));
              _2144_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2144_paramTypes, _2148_rName, ((_2142_paramFormals).Select(_2146_i)).dtor_tpe);
              _2145_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2145_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2148_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi49 = new BigInteger((_2138_values).Count);
            for (BigInteger _2149_i = BigInteger.Zero; _2149_i < _hi49; _2149_i++) {
              RAST._IType _2150_typeGen;
              RAST._IType _out586;
              _out586 = (this).GenType((((_2138_values).Select(_2149_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.InFn());
              _2150_typeGen = _out586;
              RAST._IExpr _2151_valueGen;
              DCOMP._IOwnership _2152___v213;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2153_recIdents;
              RAST._IExpr _out587;
              DCOMP._IOwnership _out588;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out589;
              (this).GenExpr(((_2138_values).Select(_2149_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out587, out _out588, out _out589);
              _2151_valueGen = _out587;
              _2152___v213 = _out588;
              _2153_recIdents = _out589;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_2138_values).Select(_2149_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2150_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2151_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2153_recIdents);
            }
            DCOMP._IEnvironment _2154_newEnv;
            _2154_newEnv = DCOMP.Environment.create(_2141_paramNames, _2144_paramTypes);
            RAST._IExpr _2155_recGen;
            DCOMP._IOwnership _2156_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2157_recIdents;
            RAST._IExpr _out590;
            DCOMP._IOwnership _out591;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out592;
            (this).GenExpr(_2140_expr, selfIdent, _2154_newEnv, expectedOwnership, out _out590, out _out591, out _out592);
            _2155_recGen = _out590;
            _2156_recOwned = _out591;
            _2157_recIdents = _out592;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2157_recIdents, _2145_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2155_recGen));
            RAST._IExpr _out593;
            DCOMP._IOwnership _out594;
            (this).FromOwnership(r, _2156_recOwned, expectedOwnership, out _out593, out _out594);
            r = _out593;
            resultingOwnership = _out594;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2158_name = _source96.dtor_ident;
          DAST._IType _2159_tpe = _source96.dtor_typ;
          DAST._IExpression _2160_value = _source96.dtor_value;
          DAST._IExpression _2161_iifeBody = _source96.dtor_iifeBody;
          {
            RAST._IExpr _2162_valueGen;
            DCOMP._IOwnership _2163___v214;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2164_recIdents;
            RAST._IExpr _out595;
            DCOMP._IOwnership _out596;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out597;
            (this).GenExpr(_2160_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out595, out _out596, out _out597);
            _2162_valueGen = _out595;
            _2163___v214 = _out596;
            _2164_recIdents = _out597;
            readIdents = _2164_recIdents;
            RAST._IType _2165_valueTypeGen;
            RAST._IType _out598;
            _out598 = (this).GenType(_2159_tpe, DCOMP.GenTypeContext.InFn());
            _2165_valueTypeGen = _out598;
            RAST._IExpr _2166_bodyGen;
            DCOMP._IOwnership _2167___v215;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2168_bodyIdents;
            RAST._IExpr _out599;
            DCOMP._IOwnership _out600;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out601;
            (this).GenExpr(_2161_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out599, out _out600, out _out601);
            _2166_bodyGen = _out599;
            _2167___v215 = _out600;
            _2168_bodyIdents = _out601;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2168_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_2158_name)))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_2158_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_2165_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2162_valueGen))).Then(_2166_bodyGen));
            RAST._IExpr _out602;
            DCOMP._IOwnership _out603;
            (this).FromOwned(r, expectedOwnership, out _out602, out _out603);
            r = _out602;
            resultingOwnership = _out603;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_Apply) {
          DAST._IExpression _2169_func = _source96.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2170_args = _source96.dtor_args;
          {
            RAST._IExpr _2171_funcExpr;
            DCOMP._IOwnership _2172___v216;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2173_recIdents;
            RAST._IExpr _out604;
            DCOMP._IOwnership _out605;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out606;
            (this).GenExpr(_2169_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out604, out _out605, out _out606);
            _2171_funcExpr = _out604;
            _2172___v216 = _out605;
            _2173_recIdents = _out606;
            readIdents = _2173_recIdents;
            Dafny.ISequence<RAST._IExpr> _2174_rArgs;
            _2174_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi50 = new BigInteger((_2170_args).Count);
            for (BigInteger _2175_i = BigInteger.Zero; _2175_i < _hi50; _2175_i++) {
              RAST._IExpr _2176_argExpr;
              DCOMP._IOwnership _2177_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2178_argIdents;
              RAST._IExpr _out607;
              DCOMP._IOwnership _out608;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out609;
              (this).GenExpr((_2170_args).Select(_2175_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out607, out _out608, out _out609);
              _2176_argExpr = _out607;
              _2177_argOwned = _out608;
              _2178_argIdents = _out609;
              _2174_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2174_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2176_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2178_argIdents);
            }
            r = (_2171_funcExpr).Apply(_2174_rArgs);
            RAST._IExpr _out610;
            DCOMP._IOwnership _out611;
            (this).FromOwned(r, expectedOwnership, out _out610, out _out611);
            r = _out610;
            resultingOwnership = _out611;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_TypeTest) {
          DAST._IExpression _2179_on = _source96.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2180_dType = _source96.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2181_variant = _source96.dtor_variant;
          {
            RAST._IExpr _2182_exprGen;
            DCOMP._IOwnership _2183___v217;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2184_recIdents;
            RAST._IExpr _out612;
            DCOMP._IOwnership _out613;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out614;
            (this).GenExpr(_2179_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out612, out _out613, out _out614);
            _2182_exprGen = _out612;
            _2183___v217 = _out613;
            _2184_recIdents = _out614;
            RAST._IType _2185_dTypePath;
            RAST._IType _out615;
            _out615 = DCOMP.COMP.GenPath(_2180_dType);
            _2185_dTypePath = _out615;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2182_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_2185_dTypePath).MSel(DCOMP.__default.escapeName(_2181_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out616;
            DCOMP._IOwnership _out617;
            (this).FromOwned(r, expectedOwnership, out _out616, out _out617);
            r = _out616;
            resultingOwnership = _out617;
            readIdents = _2184_recIdents;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_BoolBoundedPool) {
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
          goto after_match41;
        }
      }
      {
        if (_source96.is_SetBoundedPool) {
          DAST._IExpression _2186_of = _source96.dtor_of;
          {
            RAST._IExpr _2187_exprGen;
            DCOMP._IOwnership _2188___v218;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2189_recIdents;
            RAST._IExpr _out620;
            DCOMP._IOwnership _out621;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
            (this).GenExpr(_2186_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out620, out _out621, out _out622);
            _2187_exprGen = _out620;
            _2188___v218 = _out621;
            _2189_recIdents = _out622;
            r = ((_2187_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out623;
            DCOMP._IOwnership _out624;
            (this).FromOwned(r, expectedOwnership, out _out623, out _out624);
            r = _out623;
            resultingOwnership = _out624;
            readIdents = _2189_recIdents;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_SeqBoundedPool) {
          DAST._IExpression _2190_of = _source96.dtor_of;
          bool _2191_includeDuplicates = _source96.dtor_includeDuplicates;
          {
            RAST._IExpr _2192_exprGen;
            DCOMP._IOwnership _2193___v219;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2194_recIdents;
            RAST._IExpr _out625;
            DCOMP._IOwnership _out626;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out627;
            (this).GenExpr(_2190_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out625, out _out626, out _out627);
            _2192_exprGen = _out625;
            _2193___v219 = _out626;
            _2194_recIdents = _out627;
            r = ((_2192_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2191_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out628;
            DCOMP._IOwnership _out629;
            (this).FromOwned(r, expectedOwnership, out _out628, out _out629);
            r = _out628;
            resultingOwnership = _out629;
            readIdents = _2194_recIdents;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_MapBoundedPool) {
          DAST._IExpression _2195_of = _source96.dtor_of;
          {
            RAST._IExpr _2196_exprGen;
            DCOMP._IOwnership _2197___v220;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2198_recIdents;
            RAST._IExpr _out630;
            DCOMP._IOwnership _out631;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out632;
            (this).GenExpr(_2195_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out630, out _out631, out _out632);
            _2196_exprGen = _out630;
            _2197___v220 = _out631;
            _2198_recIdents = _out632;
            r = ((((_2196_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2198_recIdents;
            RAST._IExpr _out633;
            DCOMP._IOwnership _out634;
            (this).FromOwned(r, expectedOwnership, out _out633, out _out634);
            r = _out633;
            resultingOwnership = _out634;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_IntRange) {
          DAST._IExpression _2199_lo = _source96.dtor_lo;
          DAST._IExpression _2200_hi = _source96.dtor_hi;
          bool _2201_up = _source96.dtor_up;
          {
            RAST._IExpr _2202_lo;
            DCOMP._IOwnership _2203___v221;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2204_recIdentsLo;
            RAST._IExpr _out635;
            DCOMP._IOwnership _out636;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out637;
            (this).GenExpr(_2199_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out635, out _out636, out _out637);
            _2202_lo = _out635;
            _2203___v221 = _out636;
            _2204_recIdentsLo = _out637;
            RAST._IExpr _2205_hi;
            DCOMP._IOwnership _2206___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2207_recIdentsHi;
            RAST._IExpr _out638;
            DCOMP._IOwnership _out639;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out640;
            (this).GenExpr(_2200_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out638, out _out639, out _out640);
            _2205_hi = _out638;
            _2206___v222 = _out639;
            _2207_recIdentsHi = _out640;
            if (_2201_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2202_lo, _2205_hi));
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2205_hi, _2202_lo));
            }
            RAST._IExpr _out641;
            DCOMP._IOwnership _out642;
            (this).FromOwned(r, expectedOwnership, out _out641, out _out642);
            r = _out641;
            resultingOwnership = _out642;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2204_recIdentsLo, _2207_recIdentsHi);
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_UnboundedIntRange) {
          DAST._IExpression _2208_start = _source96.dtor_start;
          bool _2209_up = _source96.dtor_up;
          {
            RAST._IExpr _2210_start;
            DCOMP._IOwnership _2211___v223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2212_recIdentStart;
            RAST._IExpr _out643;
            DCOMP._IOwnership _out644;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out645;
            (this).GenExpr(_2208_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out643, out _out644, out _out645);
            _2210_start = _out643;
            _2211___v223 = _out644;
            _2212_recIdentStart = _out645;
            if (_2209_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).Apply1(_2210_start);
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).Apply1(_2210_start);
            }
            RAST._IExpr _out646;
            DCOMP._IOwnership _out647;
            (this).FromOwned(r, expectedOwnership, out _out646, out _out647);
            r = _out646;
            resultingOwnership = _out647;
            readIdents = _2212_recIdentStart;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_MapBuilder) {
          DAST._IType _2213_keyType = _source96.dtor_keyType;
          DAST._IType _2214_valueType = _source96.dtor_valueType;
          {
            RAST._IType _2215_kType;
            RAST._IType _out648;
            _out648 = (this).GenType(_2213_keyType, DCOMP.GenTypeContext.@default());
            _2215_kType = _out648;
            RAST._IType _2216_vType;
            RAST._IType _out649;
            _out649 = (this).GenType(_2214_valueType, DCOMP.GenTypeContext.@default());
            _2216_vType = _out649;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2215_kType, _2216_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out650;
            DCOMP._IOwnership _out651;
            (this).FromOwned(r, expectedOwnership, out _out650, out _out651);
            r = _out650;
            resultingOwnership = _out651;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_SetBuilder) {
          DAST._IType _2217_elemType = _source96.dtor_elemType;
          {
            RAST._IType _2218_eType;
            RAST._IType _out652;
            _out652 = (this).GenType(_2217_elemType, DCOMP.GenTypeContext.@default());
            _2218_eType = _out652;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2218_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out653;
            DCOMP._IOwnership _out654;
            (this).FromOwned(r, expectedOwnership, out _out653, out _out654);
            r = _out653;
            resultingOwnership = _out654;
            return ;
          }
          goto after_match41;
        }
      }
      {
        DAST._IType _2219_elemType = _source96.dtor_elemType;
        DAST._IExpression _2220_collection = _source96.dtor_collection;
        bool _2221_is__forall = _source96.dtor_is__forall;
        DAST._IExpression _2222_lambda = _source96.dtor_lambda;
        {
          RAST._IType _2223_tpe;
          RAST._IType _out655;
          _out655 = (this).GenType(_2219_elemType, DCOMP.GenTypeContext.@default());
          _2223_tpe = _out655;
          RAST._IExpr _2224_collectionGen;
          DCOMP._IOwnership _2225___v224;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2226_recIdents;
          RAST._IExpr _out656;
          DCOMP._IOwnership _out657;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out658;
          (this).GenExpr(_2220_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out656, out _out657, out _out658);
          _2224_collectionGen = _out656;
          _2225___v224 = _out657;
          _2226_recIdents = _out658;
          Dafny.ISequence<DAST._IAttribute> _2227_extraAttributes;
          _2227_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2220_collection).is_IntRange) || ((_2220_collection).is_UnboundedIntRange)) || ((_2220_collection).is_SeqBoundedPool)) {
            _2227_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2222_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2228_formals;
            _2228_formals = (_2222_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2229_newFormals;
            _2229_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi51 = new BigInteger((_2228_formals).Count);
            for (BigInteger _2230_i = BigInteger.Zero; _2230_i < _hi51; _2230_i++) {
              var _pat_let_tv4 = _2227_extraAttributes;
              var _pat_let_tv5 = _2228_formals;
              _2229_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2229_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2228_formals).Select(_2230_i), _pat_let34_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let34_0, _2231_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv4, ((_pat_let_tv5).Select(_2230_i)).dtor_attributes), _pat_let35_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let35_0, _2232_dt__update_hattributes_h0 => DAST.Formal.create((_2231_dt__update__tmp_h0).dtor_name, (_2231_dt__update__tmp_h0).dtor_typ, _2232_dt__update_hattributes_h0)))))));
            }
            DAST._IExpression _2233_newLambda;
            DAST._IExpression _2234_dt__update__tmp_h1 = _2222_lambda;
            Dafny.ISequence<DAST._IFormal> _2235_dt__update_hparams_h0 = _2229_newFormals;
            _2233_newLambda = DAST.Expression.create_Lambda(_2235_dt__update_hparams_h0, (_2234_dt__update__tmp_h1).dtor_retType, (_2234_dt__update__tmp_h1).dtor_body);
            RAST._IExpr _2236_lambdaGen;
            DCOMP._IOwnership _2237___v225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2238_recLambdaIdents;
            RAST._IExpr _out659;
            DCOMP._IOwnership _out660;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out661;
            (this).GenExpr(_2233_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out659, out _out660, out _out661);
            _2236_lambdaGen = _out659;
            _2237___v225 = _out660;
            _2238_recLambdaIdents = _out661;
            Dafny.ISequence<Dafny.Rune> _2239_fn;
            if (_2221_is__forall) {
              _2239_fn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all");
            } else {
              _2239_fn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any");
            }
            r = ((_2224_collectionGen).Sel(_2239_fn)).Apply1(((_2236_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2226_recIdents, _2238_recLambdaIdents);
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
    after_match41: ;
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      BigInteger _2240_i;
      _2240_i = BigInteger.Zero;
      while ((_2240_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _2241_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _2242_m;
        RAST._IMod _out664;
        _out664 = (this).GenModule((p).Select(_2240_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2242_m = _out664;
        _2241_generated = (_2242_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_2240_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2241_generated);
        _2240_i = (_2240_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2243_i;
      _2243_i = BigInteger.Zero;
      while ((_2243_i) < (new BigInteger((fullName).Count))) {
        if ((_2243_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2243_i)));
        _2243_i = (_2243_i) + (BigInteger.One);
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