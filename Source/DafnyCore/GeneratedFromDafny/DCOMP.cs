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
                Dafny.ISequence<Dafny.Rune> _1292_varName;
                _1292_varName = DCOMP.__default.escapeField(((_1290_dtor2).dtor_formal).dtor_name);
                if (((_1289_l).Sign == 0) && ((_1291_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1288_isNumeric = true;
                }
                if (_1288_isNumeric) {
                  _1291_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1290_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1289_l)));
                  _1292_varName = _1291_patternName;
                }
                if (object.Equals(((_1278_dtor).dtor_formal).dtor_name, ((_1290_dtor2).dtor_formal).dtor_name)) {
                  _1286_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1292_varName);
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
                _1285_rhs = (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("field does not exist on this variant"));
              }
              RAST._IMatchCase _1293_ctorMatch;
              _1293_ctorMatch = RAST.MatchCase.create(_1284_pattern, RAST.Expr.create_RawExpr(_1285_rhs));
              _1281_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1281_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1293_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1281_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1281_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1257_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr((this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))))));
            }
            RAST._IExpr _1294_methodBody;
            _1294_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1281_cases);
            _1273_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1273_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1279_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1280_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1294_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _1295_coerceTypes;
      _1295_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1296_rCoerceTypeParams;
      _1296_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _1297_coerceArguments;
      _1297_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _1298_coerceMap;
      _1298_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _1299_rCoerceMap;
      _1299_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1300_coerceMapToArg;
      _1300_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1301_types;
        _1301_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi18 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1302_typeI = BigInteger.Zero; _1302_typeI < _hi18; _1302_typeI++) {
          DAST._ITypeArgDecl _1303_typeParam;
          _1303_typeParam = ((c).dtor_typeParams).Select(_1302_typeI);
          DAST._IType _1304_typeArg;
          RAST._ITypeParamDecl _1305_rTypeParamDecl;
          DAST._IType _out78;
          RAST._ITypeParamDecl _out79;
          (this).GenTypeParam(_1303_typeParam, out _out78, out _out79);
          _1304_typeArg = _out78;
          _1305_rTypeParamDecl = _out79;
          RAST._IType _1306_rTypeArg;
          RAST._IType _out80;
          _out80 = (this).GenType(_1304_typeArg, DCOMP.GenTypeContext.@default());
          _1306_rTypeArg = _out80;
          _1301_types = Dafny.Sequence<RAST._IType>.Concat(_1301_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1306_rTypeArg))));
          if (((_1302_typeI) < (new BigInteger((_1259_variances).Count))) && (((_1259_variances).Select(_1302_typeI)).is_Nonvariant)) {
            _1295_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1295_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1306_rTypeArg));
            goto continue0;
          }
          DAST._ITypeArgDecl _1307_coerceTypeParam;
          DAST._ITypeArgDecl _1308_dt__update__tmp_h0 = _1303_typeParam;
          Dafny.ISequence<Dafny.Rune> _1309_dt__update_hname_h0 = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_1302_typeI));
          _1307_coerceTypeParam = DAST.TypeArgDecl.create(_1309_dt__update_hname_h0, (_1308_dt__update__tmp_h0).dtor_bounds, (_1308_dt__update__tmp_h0).dtor_variance);
          DAST._IType _1310_coerceTypeArg;
          RAST._ITypeParamDecl _1311_rCoerceTypeParamDecl;
          DAST._IType _out81;
          RAST._ITypeParamDecl _out82;
          (this).GenTypeParam(_1307_coerceTypeParam, out _out81, out _out82);
          _1310_coerceTypeArg = _out81;
          _1311_rCoerceTypeParamDecl = _out82;
          _1298_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_1298_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_1304_typeArg, _1310_coerceTypeArg)));
          RAST._IType _1312_rCoerceType;
          RAST._IType _out83;
          _out83 = (this).GenType(_1310_coerceTypeArg, DCOMP.GenTypeContext.@default());
          _1312_rCoerceType = _out83;
          _1299_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_1299_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_1306_rTypeArg, _1312_rCoerceType)));
          _1295_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1295_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1312_rCoerceType));
          _1296_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1296_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1311_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _1313_coerceFormal;
          _1313_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_1302_typeI));
          _1300_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_1300_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_1306_rTypeArg, _1312_rCoerceType), (RAST.Expr.create_Identifier(_1313_coerceFormal)).Clone())));
          _1297_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_1297_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1313_coerceFormal, RAST.__default.Rc(RAST.Type.create_IntersectionType(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_1306_rTypeArg), _1312_rCoerceType)), RAST.__default.StaticTrait)))));
        continue0: ;
        }
      after0: ;
        _1258_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1258_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1314_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1314_tpe);
})), _1301_types)))));
      }
      bool _1315_cIsEq;
      _1315_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_1315_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _1257_datatypeName, _1255_rTypeParamsDecls, _1258_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1255_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams), _1256_whereConstraints, _1273_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1316_printImplBodyCases;
      _1316_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1317_hashImplBodyCases;
      _1317_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1318_coerceImplBodyCases;
      _1318_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi19 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1319_i = BigInteger.Zero; _1319_i < _hi19; _1319_i++) {
        DAST._IDatatypeCtor _1320_ctor;
        _1320_ctor = ((c).dtor_ctors).Select(_1319_i);
        Dafny.ISequence<Dafny.Rune> _1321_ctorMatch;
        _1321_ctorMatch = DCOMP.__default.escapeName((_1320_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1322_modulePrefix;
        if (((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) {
          _1322_modulePrefix = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        } else {
          _1322_modulePrefix = Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."));
        }
        Dafny.ISequence<Dafny.Rune> _1323_ctorName;
        _1323_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1322_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1320_ctor).dtor_name));
        if (((new BigInteger((_1323_ctorName).Count)) >= (new BigInteger(13))) && (((_1323_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1323_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1324_printRhs;
        _1324_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1323_ctorName), (((_1320_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1325_hashRhs;
        _1325_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        Dafny.ISequence<RAST._IAssignIdentifier> _1326_coerceRhsArgs;
        _1326_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _1327_isNumeric;
        _1327_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1328_ctorMatchInner;
        _1328_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi20 = new BigInteger(((_1320_ctor).dtor_args).Count);
        for (BigInteger _1329_j = BigInteger.Zero; _1329_j < _hi20; _1329_j++) {
          DAST._IDatatypeDtor _1330_dtor;
          _1330_dtor = ((_1320_ctor).dtor_args).Select(_1329_j);
          Dafny.ISequence<Dafny.Rune> _1331_patternName;
          _1331_patternName = DCOMP.__default.escapeDtor(((_1330_dtor).dtor_formal).dtor_name);
          Dafny.ISequence<Dafny.Rune> _1332_fieldName;
          _1332_fieldName = DCOMP.__default.escapeField(((_1330_dtor).dtor_formal).dtor_name);
          DAST._IType _1333_formalType;
          _1333_formalType = ((_1330_dtor).dtor_formal).dtor_typ;
          if (((_1329_j).Sign == 0) && ((_1332_fieldName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1327_isNumeric = true;
          }
          if (_1327_isNumeric) {
            _1332_fieldName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1330_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1329_j)));
          }
          if ((_1333_formalType).is_Arrow) {
            _1325_hashRhs = (_1325_hashRhs).Then(((RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))));
          } else {
            _1325_hashRhs = (_1325_hashRhs).Then(((RAST.Expr.create_Identifier(_1332_fieldName)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))));
          }
          _1328_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1328_ctorMatchInner, ((_1327_isNumeric) ? (_1332_fieldName) : (_1331_patternName))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1329_j).Sign == 1) {
            _1324_printRhs = (_1324_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1324_printRhs = (_1324_printRhs).Then(RAST.Expr.create_RawExpr((((_1333_formalType).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \"<function>\")?")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1332_fieldName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))))));
          RAST._IExpr _1334_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _1335_formalTpe;
          RAST._IType _out84;
          _out84 = (this).GenType(_1333_formalType, DCOMP.GenTypeContext.@default());
          _1335_formalTpe = _out84;
          DAST._IType _1336_newFormalType;
          _1336_newFormalType = (_1333_formalType).Replace(_1298_coerceMap);
          RAST._IType _1337_newFormalTpe;
          _1337_newFormalTpe = (_1335_formalTpe).Replace(_1299_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1338_upcastConverter;
          _1338_upcastConverter = (this).UpcastConversionLambda(_1333_formalType, _1335_formalTpe, _1336_newFormalType, _1337_newFormalTpe, _1300_coerceMapToArg);
          if ((_1338_upcastConverter).is_Success) {
            RAST._IExpr _1339_coercionFunction;
            _1339_coercionFunction = (_1338_upcastConverter).dtor_value;
            _1334_coerceRhsArg = (_1339_coercionFunction).Apply1(RAST.Expr.create_Identifier(_1331_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_1329_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _1257_datatypeName));
            _1334_coerceRhsArg = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("todo!"))).Apply1(RAST.Expr.create_LiteralString((this.error).dtor_value, false, false));
          }
          _1326_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1326_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1331_patternName, _1334_coerceRhsArg)));
        }
        RAST._IExpr _1340_coerceRhs;
        _1340_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_1257_datatypeName)).MSel(DCOMP.__default.escapeName((_1320_ctor).dtor_name)), _1326_coerceRhsArgs);
        if (_1327_isNumeric) {
          _1321_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1321_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1328_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1321_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1321_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1328_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1320_ctor).dtor_hasAnyArgs) {
          _1324_printRhs = (_1324_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1324_printRhs = (_1324_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1316_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1316_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1257_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1321_ctorMatch), RAST.Expr.create_Block(_1324_printRhs))));
        _1317_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1317_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1257_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1321_ctorMatch), RAST.Expr.create_Block(_1325_hashRhs))));
        _1318_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1318_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1257_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1321_ctorMatch), RAST.Expr.create_Block(_1340_coerceRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IMatchCase> _1341_extraCases;
        _1341_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1257_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{"), (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}")))));
        _1316_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1316_printImplBodyCases, _1341_extraCases);
        _1317_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1317_hashImplBodyCases, _1341_extraCases);
        _1318_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1318_coerceImplBodyCases, _1341_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1342_defaultConstrainedTypeParams;
      _1342_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1255_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1343_rTypeParamsDeclsWithEq;
      _1343_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1255_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1344_rTypeParamsDeclsWithHash;
      _1344_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1255_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1345_printImplBody;
      _1345_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1316_printImplBodyCases);
      RAST._IExpr _1346_hashImplBody;
      _1346_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1317_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1255_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1255_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1345_printImplBody))))))));
      if ((new BigInteger((_1296_rCoerceTypeParams).Count)).Sign == 1) {
        RAST._IExpr _1347_coerceImplBody;
        _1347_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _1318_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1255_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), _1296_rCoerceTypeParams, _1297_coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams)), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1295_coerceTypes))))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.RcNew(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.Type.create_SelfOwned())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1295_coerceTypes)), _1347_coerceImplBody))))))))));
      }
      if (_1315_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1343_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1344_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1346_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1348_structName;
        _1348_structName = (RAST.Expr.create_Identifier(_1257_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1349_structAssignments;
        _1349_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi21 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1350_i = BigInteger.Zero; _1350_i < _hi21; _1350_i++) {
          DAST._IDatatypeDtor _1351_dtor;
          _1351_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1350_i);
          _1349_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1349_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1351_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1352_defaultConstrainedTypeParams;
        _1352_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1255_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1353_fullType;
        _1353_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1257_datatypeName), _1254_rTypeParams);
        if (_1315_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1352_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1353_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1353_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1348_structName, _1349_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1255_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_1353_fullType), RAST.Type.create_Borrowed(_1353_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
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
        for (BigInteger _1354_i = BigInteger.Zero; _1354_i < _hi22; _1354_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1354_i))));
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
        for (BigInteger _1355_i = BigInteger.Zero; _1355_i < _hi23; _1355_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1355_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, DCOMP._IGenTypeContext genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi24 = new BigInteger((args).Count);
      for (BigInteger _1356_i = BigInteger.Zero; _1356_i < _hi24; _1356_i++) {
        RAST._IType _1357_genTp;
        RAST._IType _out85;
        _out85 = (this).GenType((args).Select(_1356_i), genTypeContext);
        _1357_genTp = _out85;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1357_genTp));
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
          DAST._IResolvedType _1358_resolved = _source61.dtor_resolved;
          {
            RAST._IType _1359_t;
            RAST._IType _out86;
            _out86 = DCOMP.COMP.GenPath((_1358_resolved).dtor_path);
            _1359_t = _out86;
            Dafny.ISequence<RAST._IType> _1360_typeArgs;
            Dafny.ISequence<RAST._IType> _out87;
            _out87 = (this).GenTypeArgs((_1358_resolved).dtor_typeArgs, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let9_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let9_0, _1361_dt__update__tmp_h0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let10_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let10_0, _1362_dt__update_hforTraitParents_h0 => DCOMP.GenTypeContext.create((_1361_dt__update__tmp_h0).dtor_inBinding, (_1361_dt__update__tmp_h0).dtor_inFn, _1362_dt__update_hforTraitParents_h0))))));
            _1360_typeArgs = _out87;
            s = RAST.Type.create_TypeApp(_1359_t, _1360_typeArgs);
            DAST._IResolvedTypeBase _source62 = (_1358_resolved).dtor_kind;
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
                  if ((this).IsRcWrapped((_1358_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
                goto after_match9;
              }
            }
            {
              if (_source62.is_Trait) {
                {
                  if (((_1358_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
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
              DAST._IType _1363_t = _source62.dtor_baseType;
              DAST._INewtypeRange _1364_range = _source62.dtor_range;
              bool _1365_erased = _source62.dtor_erase;
              {
                if (_1365_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source63 = DCOMP.COMP.NewtypeToRustType(_1363_t, _1364_range);
                  {
                    if (_source63.is_Some) {
                      RAST._IType _1366_v = _source63.dtor_value;
                      s = _1366_v;
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
          Dafny.ISequence<DAST._IType> _1367_types = _source61.dtor_Tuple_a0;
          {
            Dafny.ISequence<RAST._IType> _1368_args;
            _1368_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1369_i;
            _1369_i = BigInteger.Zero;
            while ((_1369_i) < (new BigInteger((_1367_types).Count))) {
              RAST._IType _1370_generated;
              RAST._IType _out88;
              _out88 = (this).GenType((_1367_types).Select(_1369_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let11_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let11_0, _1371_dt__update__tmp_h1 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let12_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let12_0, _1372_dt__update_hforTraitParents_h1 => DCOMP.GenTypeContext.create((_1371_dt__update__tmp_h1).dtor_inBinding, (_1371_dt__update__tmp_h1).dtor_inFn, _1372_dt__update_hforTraitParents_h1))))));
              _1370_generated = _out88;
              _1368_args = Dafny.Sequence<RAST._IType>.Concat(_1368_args, Dafny.Sequence<RAST._IType>.FromElements(_1370_generated));
              _1369_i = (_1369_i) + (BigInteger.One);
            }
            if ((new BigInteger((_1367_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) {
              s = RAST.Type.create_TupleType(_1368_args);
            } else {
              s = RAST.__default.SystemTupleType(_1368_args);
            }
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_Array) {
          DAST._IType _1373_element = _source61.dtor_element;
          BigInteger _1374_dims = _source61.dtor_dims;
          {
            if ((_1374_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1375_elem;
              RAST._IType _out89;
              _out89 = (this).GenType(_1373_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let13_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let13_0, _1376_dt__update__tmp_h2 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let14_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let14_0, _1377_dt__update_hforTraitParents_h2 => DCOMP.GenTypeContext.create((_1376_dt__update__tmp_h2).dtor_inBinding, (_1376_dt__update__tmp_h2).dtor_inFn, _1377_dt__update_hforTraitParents_h2))))));
              _1375_elem = _out89;
              if ((_1374_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1375_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1378_n;
                _1378_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1374_dims));
                s = ((RAST.__default.dafny__runtime__type).MSel(_1378_n)).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1375_elem));
                s = (this).Object(s);
              }
            }
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_Seq) {
          DAST._IType _1379_element = _source61.dtor_element;
          {
            RAST._IType _1380_elem;
            RAST._IType _out90;
            _out90 = (this).GenType(_1379_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let15_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let15_0, _1381_dt__update__tmp_h3 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let16_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let16_0, _1382_dt__update_hforTraitParents_h3 => DCOMP.GenTypeContext.create((_1381_dt__update__tmp_h3).dtor_inBinding, (_1381_dt__update__tmp_h3).dtor_inFn, _1382_dt__update_hforTraitParents_h3))))));
            _1380_elem = _out90;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1380_elem));
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_Set) {
          DAST._IType _1383_element = _source61.dtor_element;
          {
            RAST._IType _1384_elem;
            RAST._IType _out91;
            _out91 = (this).GenType(_1383_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let17_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let17_0, _1385_dt__update__tmp_h4 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let18_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let18_0, _1386_dt__update_hforTraitParents_h4 => DCOMP.GenTypeContext.create((_1385_dt__update__tmp_h4).dtor_inBinding, (_1385_dt__update__tmp_h4).dtor_inFn, _1386_dt__update_hforTraitParents_h4))))));
            _1384_elem = _out91;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1384_elem));
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_Multiset) {
          DAST._IType _1387_element = _source61.dtor_element;
          {
            RAST._IType _1388_elem;
            RAST._IType _out92;
            _out92 = (this).GenType(_1387_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let19_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let19_0, _1389_dt__update__tmp_h5 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let20_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let20_0, _1390_dt__update_hforTraitParents_h5 => DCOMP.GenTypeContext.create((_1389_dt__update__tmp_h5).dtor_inBinding, (_1389_dt__update__tmp_h5).dtor_inFn, _1390_dt__update_hforTraitParents_h5))))));
            _1388_elem = _out92;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1388_elem));
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_Map) {
          DAST._IType _1391_key = _source61.dtor_key;
          DAST._IType _1392_value = _source61.dtor_value;
          {
            RAST._IType _1393_keyType;
            RAST._IType _out93;
            _out93 = (this).GenType(_1391_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let21_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let21_0, _1394_dt__update__tmp_h6 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let22_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let22_0, _1395_dt__update_hforTraitParents_h6 => DCOMP.GenTypeContext.create((_1394_dt__update__tmp_h6).dtor_inBinding, (_1394_dt__update__tmp_h6).dtor_inFn, _1395_dt__update_hforTraitParents_h6))))));
            _1393_keyType = _out93;
            RAST._IType _1396_valueType;
            RAST._IType _out94;
            _out94 = (this).GenType(_1392_value, genTypeContext);
            _1396_valueType = _out94;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1393_keyType, _1396_valueType));
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_MapBuilder) {
          DAST._IType _1397_key = _source61.dtor_key;
          DAST._IType _1398_value = _source61.dtor_value;
          {
            RAST._IType _1399_keyType;
            RAST._IType _out95;
            _out95 = (this).GenType(_1397_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let23_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let23_0, _1400_dt__update__tmp_h7 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let24_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let24_0, _1401_dt__update_hforTraitParents_h7 => DCOMP.GenTypeContext.create((_1400_dt__update__tmp_h7).dtor_inBinding, (_1400_dt__update__tmp_h7).dtor_inFn, _1401_dt__update_hforTraitParents_h7))))));
            _1399_keyType = _out95;
            RAST._IType _1402_valueType;
            RAST._IType _out96;
            _out96 = (this).GenType(_1398_value, genTypeContext);
            _1402_valueType = _out96;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1399_keyType, _1402_valueType));
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_SetBuilder) {
          DAST._IType _1403_elem = _source61.dtor_element;
          {
            RAST._IType _1404_elemType;
            RAST._IType _out97;
            _out97 = (this).GenType(_1403_elem, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let25_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let25_0, _1405_dt__update__tmp_h8 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let26_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let26_0, _1406_dt__update_hforTraitParents_h8 => DCOMP.GenTypeContext.create((_1405_dt__update__tmp_h8).dtor_inBinding, (_1405_dt__update__tmp_h8).dtor_inFn, _1406_dt__update_hforTraitParents_h8))))));
            _1404_elemType = _out97;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1404_elemType));
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1407_args = _source61.dtor_args;
          DAST._IType _1408_result = _source61.dtor_result;
          {
            Dafny.ISequence<RAST._IType> _1409_argTypes;
            _1409_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1410_i;
            _1410_i = BigInteger.Zero;
            while ((_1410_i) < (new BigInteger((_1407_args).Count))) {
              RAST._IType _1411_generated;
              RAST._IType _out98;
              _out98 = (this).GenType((_1407_args).Select(_1410_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let27_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let27_0, _1412_dt__update__tmp_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let28_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let28_0, _1413_dt__update_hforTraitParents_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(true, _pat_let29_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let29_0, _1414_dt__update_hinFn_h0 => DCOMP.GenTypeContext.create((_1412_dt__update__tmp_h9).dtor_inBinding, _1414_dt__update_hinFn_h0, _1413_dt__update_hforTraitParents_h9))))))));
              _1411_generated = _out98;
              _1409_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1409_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1411_generated)));
              _1410_i = (_1410_i) + (BigInteger.One);
            }
            RAST._IType _1415_resultType;
            RAST._IType _out99;
            _out99 = (this).GenType(_1408_result, DCOMP.GenTypeContext.create(((genTypeContext).dtor_inFn) || ((genTypeContext).dtor_inBinding), false, false));
            _1415_resultType = _out99;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1409_argTypes, _1415_resultType)));
          }
          goto after_match8;
        }
      }
      {
        if (_source61.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source61.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1416_name = _h90;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1416_name));
          goto after_match8;
        }
      }
      {
        if (_source61.is_Primitive) {
          DAST._IPrimitive _1417_p = _source61.dtor_Primitive_a0;
          {
            DAST._IPrimitive _source64 = _1417_p;
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
        Dafny.ISequence<Dafny.Rune> _1418_v = _source61.dtor_Passthrough_a0;
        s = RAST.__default.RawType(_1418_v);
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
      for (BigInteger _1419_i = BigInteger.Zero; _1419_i < _hi25; _1419_i++) {
        DAST._IMethod _source65 = (body).Select(_1419_i);
        {
          DAST._IMethod _1420_m = _source65;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source66 = (_1420_m).dtor_overridingPath;
            {
              if (_source66.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1421_p = _source66.dtor_value;
                {
                  Dafny.ISequence<RAST._IImplMember> _1422_existing;
                  _1422_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1421_p)) {
                    _1422_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1421_p);
                  }
                  if (((new BigInteger(((_1420_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _1423_genMethod;
                  RAST._IImplMember _out100;
                  _out100 = (this).GenMethod(_1420_m, true, enclosingType, enclosingTypeParams);
                  _1423_genMethod = _out100;
                  _1422_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1422_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1423_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1421_p, _1422_existing)));
                }
                goto after_match13;
              }
            }
            {
              {
                RAST._IImplMember _1424_generated;
                RAST._IImplMember _out101;
                _out101 = (this).GenMethod(_1420_m, forTrait, enclosingType, enclosingTypeParams);
                _1424_generated = _out101;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1424_generated));
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
      for (BigInteger _1425_i = BigInteger.Zero; _1425_i < _hi26; _1425_i++) {
        DAST._IFormal _1426_param;
        _1426_param = (@params).Select(_1425_i);
        RAST._IType _1427_paramType;
        RAST._IType _out102;
        _out102 = (this).GenType((_1426_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _1427_paramType = _out102;
        if ((!((_1427_paramType).CanReadWithoutClone())) && (!((_1426_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1427_paramType = RAST.Type.create_Borrowed(_1427_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_1426_param).dtor_name), _1427_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1428_params;
      Dafny.ISequence<RAST._IFormal> _out103;
      _out103 = (this).GenParams((m).dtor_params);
      _1428_params = _out103;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1429_paramNames;
      _1429_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1430_paramTypes;
      _1430_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi27 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1431_paramI = BigInteger.Zero; _1431_paramI < _hi27; _1431_paramI++) {
        DAST._IFormal _1432_dafny__formal;
        _1432_dafny__formal = ((m).dtor_params).Select(_1431_paramI);
        RAST._IFormal _1433_formal;
        _1433_formal = (_1428_params).Select(_1431_paramI);
        Dafny.ISequence<Dafny.Rune> _1434_name;
        _1434_name = (_1433_formal).dtor_name;
        _1429_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1429_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1434_name));
        _1430_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1430_paramTypes, _1434_name, (_1433_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1435_fnName;
      _1435_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _1436_selfIdent;
      _1436_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1437_selfId;
        _1437_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((m).dtor_outVarsAreUninitFieldsToAssign) {
          _1437_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv2 = enclosingTypeParams;
        DAST._IType _1438_instanceType;
        DAST._IType _source67 = enclosingType;
        {
          if (_source67.is_UserDefined) {
            DAST._IResolvedType _1439_r = _source67.dtor_resolved;
            _1438_instanceType = DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_1439_r, _pat_let30_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let30_0, _1440_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv2, _pat_let31_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let31_0, _1441_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_1440_dt__update__tmp_h0).dtor_path, _1441_dt__update_htypeArgs_h0, (_1440_dt__update__tmp_h0).dtor_kind, (_1440_dt__update__tmp_h0).dtor_attributes, (_1440_dt__update__tmp_h0).dtor_properMethods, (_1440_dt__update__tmp_h0).dtor_extendedTypes))))));
            goto after_match14;
          }
        }
        {
          _1438_instanceType = enclosingType;
        }
      after_match14: ;
        if (forTrait) {
          RAST._IFormal _1442_selfFormal;
          if ((m).dtor_wasFunction) {
            _1442_selfFormal = RAST.Formal.selfBorrowed;
          } else {
            _1442_selfFormal = RAST.Formal.selfBorrowedMut;
          }
          _1428_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1442_selfFormal), _1428_params);
        } else {
          RAST._IType _1443_tpe;
          RAST._IType _out104;
          _out104 = (this).GenType(_1438_instanceType, DCOMP.GenTypeContext.@default());
          _1443_tpe = _out104;
          if ((_1437_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            _1443_tpe = RAST.Type.create_Borrowed(_1443_tpe);
          } else if ((_1437_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_1443_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _1443_tpe = RAST.__default.SelfBorrowed;
              } else {
                _1443_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              if ((((enclosingType).is_UserDefined) && ((((enclosingType).dtor_resolved).dtor_kind).is_Datatype)) && ((this).IsRcWrapped(((enclosingType).dtor_resolved).dtor_attributes))) {
                _1443_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.Type.create_SelfOwned()));
              } else {
                _1443_tpe = RAST.Type.create_Borrowed(RAST.Type.create_SelfOwned());
              }
            }
          }
          _1428_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1437_selfId, _1443_tpe)), _1428_params);
        }
        _1436_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_1437_selfId, _1438_instanceType);
      }
      Dafny.ISequence<RAST._IType> _1444_retTypeArgs;
      _1444_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1445_typeI;
      _1445_typeI = BigInteger.Zero;
      while ((_1445_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1446_typeExpr;
        RAST._IType _out105;
        _out105 = (this).GenType(((m).dtor_outTypes).Select(_1445_typeI), DCOMP.GenTypeContext.@default());
        _1446_typeExpr = _out105;
        _1444_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1444_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1446_typeExpr));
        _1445_typeI = (_1445_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1447_visibility;
      if (forTrait) {
        _1447_visibility = RAST.Visibility.create_PRIV();
      } else {
        _1447_visibility = RAST.Visibility.create_PUB();
      }
      Dafny.ISequence<DAST._ITypeArgDecl> _1448_typeParamsFiltered;
      _1448_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi28 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1449_typeParamI = BigInteger.Zero; _1449_typeParamI < _hi28; _1449_typeParamI++) {
        DAST._ITypeArgDecl _1450_typeParam;
        _1450_typeParam = ((m).dtor_typeParams).Select(_1449_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1450_typeParam).dtor_name)))) {
          _1448_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1448_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1450_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1451_typeParams;
      _1451_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1448_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi29 = new BigInteger((_1448_typeParamsFiltered).Count);
        for (BigInteger _1452_i = BigInteger.Zero; _1452_i < _hi29; _1452_i++) {
          DAST._IType _1453_typeArg;
          RAST._ITypeParamDecl _1454_rTypeParamDecl;
          DAST._IType _out106;
          RAST._ITypeParamDecl _out107;
          (this).GenTypeParam((_1448_typeParamsFiltered).Select(_1452_i), out _out106, out _out107);
          _1453_typeArg = _out106;
          _1454_rTypeParamDecl = _out107;
          RAST._ITypeParamDecl _1455_dt__update__tmp_h1 = _1454_rTypeParamDecl;
          Dafny.ISequence<RAST._IType> _1456_dt__update_hconstraints_h0 = Dafny.Sequence<RAST._IType>.Concat((_1454_rTypeParamDecl).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
          _1454_rTypeParamDecl = RAST.TypeParamDecl.create((_1455_dt__update__tmp_h1).dtor_content, _1456_dt__update_hconstraints_h0);
          _1451_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1451_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1454_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1457_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1458_env = DCOMP.Environment.Default();
      RAST._IExpr _1459_preBody;
      _1459_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1460_preAssignNames;
      _1460_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1461_preAssignTypes;
      _1461_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1462_earlyReturn;
        _1462_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None();
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source68 = (m).dtor_outVars;
        {
          if (_source68.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1463_outVars = _source68.dtor_value;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1462_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
                BigInteger _hi30 = new BigInteger((_1463_outVars).Count);
                for (BigInteger _1464_outI = BigInteger.Zero; _1464_outI < _hi30; _1464_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1465_outVar;
                  _1465_outVar = (_1463_outVars).Select(_1464_outI);
                  Dafny.ISequence<Dafny.Rune> _1466_outName;
                  _1466_outName = DCOMP.__default.escapeName((_1465_outVar));
                  Dafny.ISequence<Dafny.Rune> _1467_tracker__name;
                  _1467_tracker__name = DCOMP.__default.AddAssignedPrefix(_1466_outName);
                  _1460_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1460_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1467_tracker__name));
                  _1461_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1461_preAssignTypes, _1467_tracker__name, RAST.Type.create_Bool());
                  _1459_preBody = (_1459_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1467_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1468_tupleArgs;
                _1468_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
                BigInteger _hi31 = new BigInteger((_1463_outVars).Count);
                for (BigInteger _1469_outI = BigInteger.Zero; _1469_outI < _hi31; _1469_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1470_outVar;
                  _1470_outVar = (_1463_outVars).Select(_1469_outI);
                  RAST._IType _1471_outType;
                  RAST._IType _out108;
                  _out108 = (this).GenType(((m).dtor_outTypes).Select(_1469_outI), DCOMP.GenTypeContext.@default());
                  _1471_outType = _out108;
                  Dafny.ISequence<Dafny.Rune> _1472_outName;
                  _1472_outName = DCOMP.__default.escapeName((_1470_outVar));
                  _1429_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1429_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1472_outName));
                  RAST._IType _1473_outMaybeType;
                  if ((_1471_outType).CanReadWithoutClone()) {
                    _1473_outMaybeType = _1471_outType;
                  } else {
                    _1473_outMaybeType = RAST.__default.MaybePlaceboType(_1471_outType);
                  }
                  _1430_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1430_paramTypes, _1472_outName, _1473_outMaybeType);
                  _1468_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1468_tupleArgs, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1472_outName));
                }
                _1462_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(_1468_tupleArgs);
              }
            }
            goto after_match15;
          }
        }
        {
        }
      after_match15: ;
        _1458_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1460_preAssignNames, _1429_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1461_preAssignTypes, _1430_paramTypes));
        RAST._IExpr _1474_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1475___v69;
        DCOMP._IEnvironment _1476___v70;
        RAST._IExpr _out109;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out110;
        DCOMP._IEnvironment _out111;
        (this).GenStmts((m).dtor_body, _1436_selfIdent, _1458_env, true, _1462_earlyReturn, out _out109, out _out110, out _out111);
        _1474_body = _out109;
        _1475___v69 = _out110;
        _1476___v70 = _out111;
        _1457_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1459_preBody).Then(_1474_body));
      } else {
        _1458_env = DCOMP.Environment.create(_1429_paramNames, _1430_paramTypes);
        _1457_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1447_visibility, RAST.Fn.create(_1435_fnName, _1451_typeParams, _1428_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1444_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1444_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1444_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1457_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1477_declarations;
      _1477_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1478_i;
      _1478_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1479_stmts;
      _1479_stmts = stmts;
      while ((_1478_i) < (new BigInteger((_1479_stmts).Count))) {
        DAST._IStatement _1480_stmt;
        _1480_stmt = (_1479_stmts).Select(_1478_i);
        DAST._IStatement _source69 = _1480_stmt;
        {
          if (_source69.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1481_name = _source69.dtor_name;
            DAST._IType _1482_optType = _source69.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source69.dtor_maybeValue;
            if (maybeValue0.is_None) {
              if (((_1478_i) + (BigInteger.One)) < (new BigInteger((_1479_stmts).Count))) {
                DAST._IStatement _source70 = (_1479_stmts).Select((_1478_i) + (BigInteger.One));
                {
                  if (_source70.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source70.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> ident0 = lhs0.dtor_ident;
                      Dafny.ISequence<Dafny.Rune> _1483_name2 = ident0;
                      DAST._IExpression _1484_rhs = _source70.dtor_value;
                      if (object.Equals(_1483_name2, _1481_name)) {
                        _1479_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1479_stmts).Subsequence(BigInteger.Zero, _1478_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1481_name, _1482_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1484_rhs)))), (_1479_stmts).Drop((_1478_i) + (new BigInteger(2))));
                        _1480_stmt = (_1479_stmts).Select(_1478_i);
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
        RAST._IExpr _1485_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1486_recIdents;
        DCOMP._IEnvironment _1487_newEnv2;
        RAST._IExpr _out112;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out113;
        DCOMP._IEnvironment _out114;
        (this).GenStmt(_1480_stmt, selfIdent, newEnv, (isLast) && ((_1478_i) == ((new BigInteger((_1479_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out112, out _out113, out _out114);
        _1485_stmtExpr = _out112;
        _1486_recIdents = _out113;
        _1487_newEnv2 = _out114;
        newEnv = _1487_newEnv2;
        DAST._IStatement _source71 = _1480_stmt;
        {
          if (_source71.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1488_name = _source71.dtor_name;
            {
              _1477_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1477_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_1488_name)));
            }
            goto after_match18;
          }
        }
        {
        }
      after_match18: ;
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1486_recIdents, _1477_declarations));
        generated = (generated).Then(_1485_stmtExpr);
        _1478_i = (_1478_i) + (BigInteger.One);
        if ((_1485_stmtExpr).is_Return) {
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
          Dafny.ISequence<Dafny.Rune> _1489_id = ident1;
          {
            Dafny.ISequence<Dafny.Rune> _1490_idRust;
            _1490_idRust = DCOMP.__default.escapeName(_1489_id);
            if (((env).IsBorrowed(_1490_idRust)) || ((env).IsBorrowedMut(_1490_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1490_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1490_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1490_idRust);
            needsIIFE = false;
          }
          goto after_match19;
        }
      }
      {
        if (_source72.is_Select) {
          DAST._IExpression _1491_on = _source72.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1492_field = _source72.dtor_field;
          {
            Dafny.ISequence<Dafny.Rune> _1493_fieldName;
            _1493_fieldName = DCOMP.__default.escapeName(_1492_field);
            RAST._IExpr _1494_onExpr;
            DCOMP._IOwnership _1495_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1496_recIdents;
            RAST._IExpr _out115;
            DCOMP._IOwnership _out116;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out117;
            (this).GenExpr(_1491_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out115, out _out116, out _out117);
            _1494_onExpr = _out115;
            _1495_onOwned = _out116;
            _1496_recIdents = _out117;
            RAST._IExpr _source73 = _1494_onExpr;
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
                Dafny.ISequence<Dafny.Rune> _1497_isAssignedVar;
                _1497_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1493_fieldName);
                if (((newEnv).dtor_names).Contains(_1497_isAssignedVar)) {
                  generated = ((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1493_fieldName), RAST.Expr.create_Identifier(_1497_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1497_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _1497_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _1493_fieldName, rhs);
                }
                goto after_match20;
              }
            }
            {
              if (!object.Equals(_1494_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _1494_onExpr = ((this).modify__macro).Apply1(_1494_onExpr);
              }
              generated = RAST.__default.AssignMember(_1494_onExpr, _1493_fieldName, rhs);
            }
          after_match20: ;
            readIdents = _1496_recIdents;
            needsIIFE = false;
          }
          goto after_match19;
        }
      }
      {
        DAST._IExpression _1498_on = _source72.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1499_indices = _source72.dtor_indices;
        {
          RAST._IExpr _1500_onExpr;
          DCOMP._IOwnership _1501_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1502_recIdents;
          RAST._IExpr _out118;
          DCOMP._IOwnership _out119;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out120;
          (this).GenExpr(_1498_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out118, out _out119, out _out120);
          _1500_onExpr = _out118;
          _1501_onOwned = _out119;
          _1502_recIdents = _out120;
          readIdents = _1502_recIdents;
          _1500_onExpr = ((this).modify__macro).Apply1(_1500_onExpr);
          RAST._IExpr _1503_r;
          _1503_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1504_indicesExpr;
          _1504_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi32 = new BigInteger((_1499_indices).Count);
          for (BigInteger _1505_i = BigInteger.Zero; _1505_i < _hi32; _1505_i++) {
            RAST._IExpr _1506_idx;
            DCOMP._IOwnership _1507___v79;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1508_recIdentsIdx;
            RAST._IExpr _out121;
            DCOMP._IOwnership _out122;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out123;
            (this).GenExpr((_1499_indices).Select(_1505_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out121, out _out122, out _out123);
            _1506_idx = _out121;
            _1507___v79 = _out122;
            _1508_recIdentsIdx = _out123;
            Dafny.ISequence<Dafny.Rune> _1509_varName;
            _1509_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1505_i));
            _1504_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1504_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1509_varName)));
            _1503_r = (_1503_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1509_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.IntoUsize(_1506_idx))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1508_recIdentsIdx);
          }
          if ((new BigInteger((_1499_indices).Count)) > (BigInteger.One)) {
            _1500_onExpr = (_1500_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1510_rhs;
          _1510_rhs = rhs;
          var _pat_let_tv3 = env;
          if (((_1500_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1500_onExpr).LhsIdentifierName(), _pat_let32_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let32_0, _1511_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv3).GetType(_1511_name), _pat_let33_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let33_0, _1512_tpe => ((_1512_tpe).is_Some) && (((_1512_tpe).dtor_value).IsUninitArray())))))))) {
            _1510_rhs = RAST.__default.MaybeUninitNew(_1510_rhs);
          }
          generated = (_1503_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1500_onExpr, _1504_indicesExpr)), _1510_rhs));
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
          Dafny.ISequence<DAST._IFormal> _1513_fields = _source74.dtor_fields;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi33 = new BigInteger((_1513_fields).Count);
            for (BigInteger _1514_i = BigInteger.Zero; _1514_i < _hi33; _1514_i++) {
              DAST._IFormal _1515_field;
              _1515_field = (_1513_fields).Select(_1514_i);
              Dafny.ISequence<Dafny.Rune> _1516_fieldName;
              _1516_fieldName = DCOMP.__default.escapeName((_1515_field).dtor_name);
              RAST._IType _1517_fieldTyp;
              RAST._IType _out124;
              _out124 = (this).GenType((_1515_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _1517_fieldTyp = _out124;
              Dafny.ISequence<Dafny.Rune> _1518_isAssignedVar;
              _1518_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1516_fieldName);
              if (((newEnv).dtor_names).Contains(_1518_isAssignedVar)) {
                RAST._IExpr _1519_rhs;
                DCOMP._IOwnership _1520___v80;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1521___v81;
                RAST._IExpr _out125;
                DCOMP._IOwnership _out126;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out127;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1515_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out125, out _out126, out _out127);
                _1519_rhs = _out125;
                _1520___v80 = _out126;
                _1521___v81 = _out127;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1518_isAssignedVar));
                generated = (generated).Then(((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1516_fieldName), RAST.Expr.create_Identifier(_1518_isAssignedVar), _1519_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1518_isAssignedVar);
              }
            }
          }
          goto after_match21;
        }
      }
      {
        if (_source74.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1522_name = _source74.dtor_name;
          DAST._IType _1523_typ = _source74.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source74.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1524_expression = maybeValue1.dtor_value;
            {
              RAST._IType _1525_tpe;
              RAST._IType _out128;
              _out128 = (this).GenType(_1523_typ, DCOMP.GenTypeContext.InBinding());
              _1525_tpe = _out128;
              Dafny.ISequence<Dafny.Rune> _1526_varName;
              _1526_varName = DCOMP.__default.escapeName(_1522_name);
              bool _1527_hasCopySemantics;
              _1527_hasCopySemantics = (_1525_tpe).CanReadWithoutClone();
              if (((_1524_expression).is_InitializationValue) && (!(_1527_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1526_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).ApplyType1(_1525_tpe)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1526_varName, RAST.__default.MaybePlaceboType(_1525_tpe));
              } else {
                RAST._IExpr _1528_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1529_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1524_expression).is_InitializationValue) && ((_1525_tpe).IsObjectOrPointer())) {
                  _1528_expr = (_1525_tpe).ToNullExpr();
                  _1529_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1530_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out129;
                  DCOMP._IOwnership _out130;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
                  (this).GenExpr(_1524_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out129, out _out130, out _out131);
                  _1528_expr = _out129;
                  _1530_exprOwnership = _out130;
                  _1529_recIdents = _out131;
                }
                readIdents = _1529_recIdents;
                if ((_1524_expression).is_NewUninitArray) {
                  _1525_tpe = (_1525_tpe).TypeAtInitialization();
                } else {
                  _1525_tpe = _1525_tpe;
                }
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_1522_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1525_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1528_expr));
                newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_1522_name), _1525_tpe);
              }
            }
            goto after_match21;
          }
        }
      }
      {
        if (_source74.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1531_name = _source74.dtor_name;
          DAST._IType _1532_typ = _source74.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source74.dtor_maybeValue;
          if (maybeValue2.is_None) {
            {
              DAST._IStatement _1533_newStmt;
              _1533_newStmt = DAST.Statement.create_DeclareVar(_1531_name, _1532_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1532_typ)));
              RAST._IExpr _out132;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out133;
              DCOMP._IEnvironment _out134;
              (this).GenStmt(_1533_newStmt, selfIdent, env, isLast, earlyReturn, out _out132, out _out133, out _out134);
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
          DAST._IAssignLhs _1534_lhs = _source74.dtor_lhs;
          DAST._IExpression _1535_expression = _source74.dtor_value;
          {
            RAST._IExpr _1536_exprGen;
            DCOMP._IOwnership _1537___v82;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1538_exprIdents;
            RAST._IExpr _out135;
            DCOMP._IOwnership _out136;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
            (this).GenExpr(_1535_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out135, out _out136, out _out137);
            _1536_exprGen = _out135;
            _1537___v82 = _out136;
            _1538_exprIdents = _out137;
            if ((_1534_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1539_rustId;
              _1539_rustId = DCOMP.__default.escapeName(((_1534_lhs).dtor_ident));
              Std.Wrappers._IOption<RAST._IType> _1540_tpe;
              _1540_tpe = (env).GetType(_1539_rustId);
              if (((_1540_tpe).is_Some) && ((((_1540_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1536_exprGen = RAST.__default.MaybePlacebo(_1536_exprGen);
              }
            }
            if (((_1534_lhs).is_Index) && (((_1534_lhs).dtor_expr).is_Ident)) {
              Dafny.ISequence<Dafny.Rune> _1541_rustId;
              _1541_rustId = DCOMP.__default.escapeName(((_1534_lhs).dtor_expr).dtor_name);
              Std.Wrappers._IOption<RAST._IType> _1542_tpe;
              _1542_tpe = (env).GetType(_1541_rustId);
              if (((_1542_tpe).is_Some) && ((((_1542_tpe).dtor_value).ExtractMaybeUninitArrayElement()).is_Some)) {
                _1536_exprGen = RAST.__default.MaybeUninitNew(_1536_exprGen);
              }
            }
            RAST._IExpr _1543_lhsGen;
            bool _1544_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1545_recIdents;
            DCOMP._IEnvironment _1546_resEnv;
            RAST._IExpr _out138;
            bool _out139;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out140;
            DCOMP._IEnvironment _out141;
            (this).GenAssignLhs(_1534_lhs, _1536_exprGen, selfIdent, env, out _out138, out _out139, out _out140, out _out141);
            _1543_lhsGen = _out138;
            _1544_needsIIFE = _out139;
            _1545_recIdents = _out140;
            _1546_resEnv = _out141;
            generated = _1543_lhsGen;
            newEnv = _1546_resEnv;
            if (_1544_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1545_recIdents, _1538_exprIdents);
          }
          goto after_match21;
        }
      }
      {
        if (_source74.is_If) {
          DAST._IExpression _1547_cond = _source74.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1548_thnDafny = _source74.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1549_elsDafny = _source74.dtor_els;
          {
            RAST._IExpr _1550_cond;
            DCOMP._IOwnership _1551___v83;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1552_recIdents;
            RAST._IExpr _out142;
            DCOMP._IOwnership _out143;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
            (this).GenExpr(_1547_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out142, out _out143, out _out144);
            _1550_cond = _out142;
            _1551___v83 = _out143;
            _1552_recIdents = _out144;
            Dafny.ISequence<Dafny.Rune> _1553_condString;
            _1553_condString = (_1550_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1552_recIdents;
            RAST._IExpr _1554_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1555_thnIdents;
            DCOMP._IEnvironment _1556_thnEnv;
            RAST._IExpr _out145;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out146;
            DCOMP._IEnvironment _out147;
            (this).GenStmts(_1548_thnDafny, selfIdent, env, isLast, earlyReturn, out _out145, out _out146, out _out147);
            _1554_thn = _out145;
            _1555_thnIdents = _out146;
            _1556_thnEnv = _out147;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1555_thnIdents);
            RAST._IExpr _1557_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1558_elsIdents;
            DCOMP._IEnvironment _1559_elsEnv;
            RAST._IExpr _out148;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out149;
            DCOMP._IEnvironment _out150;
            (this).GenStmts(_1549_elsDafny, selfIdent, env, isLast, earlyReturn, out _out148, out _out149, out _out150);
            _1557_els = _out148;
            _1558_elsIdents = _out149;
            _1559_elsEnv = _out150;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1558_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1550_cond, _1554_thn, _1557_els);
          }
          goto after_match21;
        }
      }
      {
        if (_source74.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1560_lbl = _source74.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1561_body = _source74.dtor_body;
          {
            RAST._IExpr _1562_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1563_bodyIdents;
            DCOMP._IEnvironment _1564_env2;
            RAST._IExpr _out151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out152;
            DCOMP._IEnvironment _out153;
            (this).GenStmts(_1561_body, selfIdent, env, isLast, earlyReturn, out _out151, out _out152, out _out153);
            _1562_body = _out151;
            _1563_bodyIdents = _out152;
            _1564_env2 = _out153;
            readIdents = _1563_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1560_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1562_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
          goto after_match21;
        }
      }
      {
        if (_source74.is_While) {
          DAST._IExpression _1565_cond = _source74.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1566_body = _source74.dtor_body;
          {
            RAST._IExpr _1567_cond;
            DCOMP._IOwnership _1568___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1569_recIdents;
            RAST._IExpr _out154;
            DCOMP._IOwnership _out155;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
            (this).GenExpr(_1565_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out154, out _out155, out _out156);
            _1567_cond = _out154;
            _1568___v84 = _out155;
            _1569_recIdents = _out156;
            readIdents = _1569_recIdents;
            RAST._IExpr _1570_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1571_bodyIdents;
            DCOMP._IEnvironment _1572_bodyEnv;
            RAST._IExpr _out157;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out158;
            DCOMP._IEnvironment _out159;
            (this).GenStmts(_1566_body, selfIdent, env, false, earlyReturn, out _out157, out _out158, out _out159);
            _1570_bodyExpr = _out157;
            _1571_bodyIdents = _out158;
            _1572_bodyEnv = _out159;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1571_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1567_cond), _1570_bodyExpr);
          }
          goto after_match21;
        }
      }
      {
        if (_source74.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1573_boundName = _source74.dtor_boundName;
          DAST._IType _1574_boundType = _source74.dtor_boundType;
          DAST._IExpression _1575_overExpr = _source74.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1576_body = _source74.dtor_body;
          {
            RAST._IExpr _1577_over;
            DCOMP._IOwnership _1578___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1579_recIdents;
            RAST._IExpr _out160;
            DCOMP._IOwnership _out161;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out162;
            (this).GenExpr(_1575_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out160, out _out161, out _out162);
            _1577_over = _out160;
            _1578___v85 = _out161;
            _1579_recIdents = _out162;
            if (((_1575_overExpr).is_MapBoundedPool) || ((_1575_overExpr).is_SetBoundedPool)) {
              _1577_over = ((_1577_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1580_boundTpe;
            RAST._IType _out163;
            _out163 = (this).GenType(_1574_boundType, DCOMP.GenTypeContext.@default());
            _1580_boundTpe = _out163;
            readIdents = _1579_recIdents;
            Dafny.ISequence<Dafny.Rune> _1581_boundRName;
            _1581_boundRName = DCOMP.__default.escapeName(_1573_boundName);
            RAST._IExpr _1582_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1583_bodyIdents;
            DCOMP._IEnvironment _1584_bodyEnv;
            RAST._IExpr _out164;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out165;
            DCOMP._IEnvironment _out166;
            (this).GenStmts(_1576_body, selfIdent, (env).AddAssigned(_1581_boundRName, _1580_boundTpe), false, earlyReturn, out _out164, out _out165, out _out166);
            _1582_bodyExpr = _out164;
            _1583_bodyIdents = _out165;
            _1584_bodyEnv = _out166;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1583_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1581_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1581_boundRName, _1577_over, _1582_bodyExpr);
          }
          goto after_match21;
        }
      }
      {
        if (_source74.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1585_toLabel = _source74.dtor_toLabel;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source75 = _1585_toLabel;
            {
              if (_source75.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1586_lbl = _source75.dtor_value;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1586_lbl)));
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
          Dafny.ISequence<DAST._IStatement> _1587_body = _source74.dtor_body;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _1588_selfClone;
              DCOMP._IOwnership _1589___v86;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1590___v87;
              RAST._IExpr _out167;
              DCOMP._IOwnership _out168;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out169;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out167, out _out168, out _out169);
              _1588_selfClone = _out167;
              _1589___v86 = _out168;
              _1590___v87 = _out169;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1588_selfClone)));
            }
            newEnv = env;
            BigInteger _hi34 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1591_paramI = BigInteger.Zero; _1591_paramI < _hi34; _1591_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1592_param;
              _1592_param = ((env).dtor_names).Select(_1591_paramI);
              RAST._IExpr _1593_paramInit;
              DCOMP._IOwnership _1594___v88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1595___v89;
              RAST._IExpr _out170;
              DCOMP._IOwnership _out171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out172;
              (this).GenIdent(_1592_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out170, out _out171, out _out172);
              _1593_paramInit = _out170;
              _1594___v88 = _out171;
              _1595___v89 = _out172;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1592_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1593_paramInit)));
              if (((env).dtor_types).Contains(_1592_param)) {
                RAST._IType _1596_declaredType;
                _1596_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1592_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1592_param, _1596_declaredType);
              }
            }
            RAST._IExpr _1597_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1598_bodyIdents;
            DCOMP._IEnvironment _1599_bodyEnv;
            RAST._IExpr _out173;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out174;
            DCOMP._IEnvironment _out175;
            (this).GenStmts(_1587_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out173, out _out174, out _out175);
            _1597_bodyExpr = _out173;
            _1598_bodyIdents = _out174;
            _1599_bodyEnv = _out175;
            readIdents = _1598_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1597_bodyExpr)));
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
          DAST._IExpression _1600_on = _source74.dtor_on;
          DAST._ICallName _1601_name = _source74.dtor_callName;
          Dafny.ISequence<DAST._IType> _1602_typeArgs = _source74.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1603_args = _source74.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1604_maybeOutVars = _source74.dtor_outs;
          {
            Dafny.ISequence<RAST._IExpr> _1605_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1606_recIdents;
            Dafny.ISequence<RAST._IType> _1607_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _1608_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out176;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
            Dafny.ISequence<RAST._IType> _out178;
            Std.Wrappers._IOption<DAST._IResolvedType> _out179;
            (this).GenArgs(selfIdent, _1601_name, _1602_typeArgs, _1603_args, env, out _out176, out _out177, out _out178, out _out179);
            _1605_argExprs = _out176;
            _1606_recIdents = _out177;
            _1607_typeExprs = _out178;
            _1608_fullNameQualifier = _out179;
            readIdents = _1606_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source76 = _1608_fullNameQualifier;
            {
              if (_source76.is_Some) {
                DAST._IResolvedType value9 = _source76.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1609_path = value9.dtor_path;
                Dafny.ISequence<DAST._IType> _1610_onTypeArgs = value9.dtor_typeArgs;
                DAST._IResolvedTypeBase _1611_base = value9.dtor_kind;
                RAST._IExpr _1612_fullPath;
                RAST._IExpr _out180;
                _out180 = DCOMP.COMP.GenPathExpr(_1609_path);
                _1612_fullPath = _out180;
                Dafny.ISequence<RAST._IType> _1613_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out181;
                _out181 = (this).GenTypeArgs(_1610_onTypeArgs, DCOMP.GenTypeContext.@default());
                _1613_onTypeExprs = _out181;
                RAST._IExpr _1614_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _1615_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1616_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1611_base).is_Trait) || ((_1611_base).is_Class)) {
                  RAST._IExpr _out182;
                  DCOMP._IOwnership _out183;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out184;
                  (this).GenExpr(_1600_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out182, out _out183, out _out184);
                  _1614_onExpr = _out182;
                  _1615_recOwnership = _out183;
                  _1616_recIdents = _out184;
                  _1614_onExpr = ((this).modify__macro).Apply1(_1614_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1616_recIdents);
                } else {
                  RAST._IExpr _out185;
                  DCOMP._IOwnership _out186;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out187;
                  (this).GenExpr(_1600_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out185, out _out186, out _out187);
                  _1614_onExpr = _out185;
                  _1615_recOwnership = _out186;
                  _1616_recIdents = _out187;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1616_recIdents);
                }
                generated = ((((_1612_fullPath).ApplyType(_1613_onTypeExprs)).MSel(DCOMP.__default.escapeName((_1601_name).dtor_name))).ApplyType(_1607_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_1614_onExpr), _1605_argExprs));
                goto after_match23;
              }
            }
            {
              RAST._IExpr _1617_onExpr;
              DCOMP._IOwnership _1618___v94;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1619_enclosingIdents;
              RAST._IExpr _out188;
              DCOMP._IOwnership _out189;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out190;
              (this).GenExpr(_1600_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out188, out _out189, out _out190);
              _1617_onExpr = _out188;
              _1618___v94 = _out189;
              _1619_enclosingIdents = _out190;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1619_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _1620_renderedName;
              DAST._ICallName _source77 = _1601_name;
              {
                if (_source77.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _1621_name = _source77.dtor_name;
                  _1620_renderedName = DCOMP.__default.escapeName(_1621_name);
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
                  _1620_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                  goto after_match24;
                }
              }
              {
                _1620_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
              }
            after_match24: ;
              DAST._IExpression _source78 = _1600_on;
              {
                if (_source78.is_Companion) {
                  {
                    _1617_onExpr = (_1617_onExpr).MSel(_1620_renderedName);
                  }
                  goto after_match25;
                }
              }
              {
                {
                  if (!object.Equals(_1617_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source79 = _1601_name;
                    {
                      if (_source79.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source79.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _1622_tpe = onType0.dtor_value;
                          RAST._IType _1623_typ;
                          RAST._IType _out191;
                          _out191 = (this).GenType(_1622_tpe, DCOMP.GenTypeContext.@default());
                          _1623_typ = _out191;
                          if (((_1623_typ).IsObjectOrPointer()) && (!object.Equals(_1617_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _1617_onExpr = ((this).modify__macro).Apply1(_1617_onExpr);
                          }
                          goto after_match26;
                        }
                      }
                    }
                    {
                    }
                  after_match26: ;
                  }
                  _1617_onExpr = (_1617_onExpr).Sel(_1620_renderedName);
                }
              }
            after_match25: ;
              generated = ((_1617_onExpr).ApplyType(_1607_typeExprs)).Apply(_1605_argExprs);
            }
          after_match23: ;
            if (((_1604_maybeOutVars).is_Some) && ((new BigInteger(((_1604_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1624_outVar;
              _1624_outVar = DCOMP.__default.escapeName((((_1604_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
              if (!((env).CanReadWithoutClone(_1624_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1624_outVar, generated);
            } else if (((_1604_maybeOutVars).is_None) || ((new BigInteger(((_1604_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1625_tmpVar;
              _1625_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1626_tmpId;
              _1626_tmpId = RAST.Expr.create_Identifier(_1625_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1625_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1627_outVars;
              _1627_outVars = (_1604_maybeOutVars).dtor_value;
              BigInteger _hi35 = new BigInteger((_1627_outVars).Count);
              for (BigInteger _1628_outI = BigInteger.Zero; _1628_outI < _hi35; _1628_outI++) {
                Dafny.ISequence<Dafny.Rune> _1629_outVar;
                _1629_outVar = DCOMP.__default.escapeName(((_1627_outVars).Select(_1628_outI)));
                RAST._IExpr _1630_rhs;
                _1630_rhs = (_1626_tmpId).Sel(Std.Strings.__default.OfNat(_1628_outI));
                if (!((env).CanReadWithoutClone(_1629_outVar))) {
                  _1630_rhs = RAST.__default.MaybePlacebo(_1630_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1629_outVar, _1630_rhs));
              }
            }
            newEnv = env;
          }
          goto after_match21;
        }
      }
      {
        if (_source74.is_Return) {
          DAST._IExpression _1631_exprDafny = _source74.dtor_expr;
          {
            RAST._IExpr _1632_expr;
            DCOMP._IOwnership _1633___v105;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1634_recIdents;
            RAST._IExpr _out192;
            DCOMP._IOwnership _out193;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out194;
            (this).GenExpr(_1631_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out192, out _out193, out _out194);
            _1632_expr = _out192;
            _1633___v105 = _out193;
            _1634_recIdents = _out194;
            readIdents = _1634_recIdents;
            if (isLast) {
              generated = _1632_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1632_expr));
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
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1635_rustIdents = _source80.dtor_value;
              Dafny.ISequence<RAST._IExpr> _1636_tupleArgs;
              _1636_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi36 = new BigInteger((_1635_rustIdents).Count);
              for (BigInteger _1637_i = BigInteger.Zero; _1637_i < _hi36; _1637_i++) {
                RAST._IExpr _1638_rIdent;
                DCOMP._IOwnership _1639___v106;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1640___v107;
                RAST._IExpr _out195;
                DCOMP._IOwnership _out196;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out197;
                (this).GenIdent((_1635_rustIdents).Select(_1637_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out195, out _out196, out _out197);
                _1638_rIdent = _out195;
                _1639___v106 = _out196;
                _1640___v107 = _out197;
                _1636_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1636_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1638_rIdent));
              }
              if ((new BigInteger((_1636_tupleArgs).Count)) == (BigInteger.One)) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1636_tupleArgs).Select(BigInteger.Zero)));
              } else {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1636_tupleArgs)));
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
        DAST._IExpression _1641_e = _source74.dtor_Print_a0;
        {
          RAST._IExpr _1642_printedExpr;
          DCOMP._IOwnership _1643_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1644_recIdents;
          RAST._IExpr _out198;
          DCOMP._IOwnership _out199;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out200;
          (this).GenExpr(_1641_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out198, out _out199, out _out200);
          _1642_printedExpr = _out198;
          _1643_recOwnership = _out199;
          _1644_recIdents = _out200;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1642_printedExpr)));
          readIdents = _1644_recIdents;
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
            bool _1645_b = _h170.dtor_BoolLiteral_a0;
            {
              RAST._IExpr _out205;
              DCOMP._IOwnership _out206;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_1645_b), expectedOwnership, out _out205, out _out206);
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
            Dafny.ISequence<Dafny.Rune> _1646_i = _h171.dtor_IntLiteral_a0;
            DAST._IType _1647_t = _h171.dtor_IntLiteral_a1;
            {
              DAST._IType _source83 = _1647_t;
              {
                if (_source83.is_Primitive) {
                  DAST._IPrimitive _h70 = _source83.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    {
                      if ((new BigInteger((_1646_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1646_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1646_i, true, false));
                      }
                    }
                    goto after_match29;
                  }
                }
              }
              {
                DAST._IType _1648_o = _source83;
                {
                  RAST._IType _1649_genType;
                  RAST._IType _out207;
                  _out207 = (this).GenType(_1648_o, DCOMP.GenTypeContext.@default());
                  _1649_genType = _out207;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1646_i), _1649_genType);
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
            Dafny.ISequence<Dafny.Rune> _1650_n = _h172.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1651_d = _h172.dtor_DecLiteral_a1;
            DAST._IType _1652_t = _h172.dtor_DecLiteral_a2;
            {
              DAST._IType _source84 = _1652_t;
              {
                if (_source84.is_Primitive) {
                  DAST._IPrimitive _h71 = _source84.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1650_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1651_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                    goto after_match30;
                  }
                }
              }
              {
                DAST._IType _1653_o = _source84;
                {
                  RAST._IType _1654_genType;
                  RAST._IType _out210;
                  _out210 = (this).GenType(_1653_o, DCOMP.GenTypeContext.@default());
                  _1654_genType = _out210;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1650_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1651_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1654_genType);
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
            Dafny.ISequence<Dafny.Rune> _1655_l = _h173.dtor_StringLiteral_a0;
            bool _1656_verbatim = _h173.dtor_verbatim;
            {
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1655_l, false, _1656_verbatim));
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
            BigInteger _1657_c = _h174.dtor_CharLiteralUTF16_a0;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1657_c));
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
            Dafny.Rune _1658_c = _h175.dtor_CharLiteral_a0;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1658_c).Value)));
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
        DAST._IType _1659_tpe = _h176.dtor_Null_a0;
        {
          RAST._IType _1660_tpeGen;
          RAST._IType _out219;
          _out219 = (this).GenType(_1659_tpe, DCOMP.GenTypeContext.@default());
          _1660_tpeGen = _out219;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null"));
          } else {
            r = RAST.Expr.create_TypeAscription(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _1660_tpeGen);
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
      DAST._IBinOp _1661_op = _let_tmp_rhs54.dtor_op;
      DAST._IExpression _1662_lExpr = _let_tmp_rhs54.dtor_left;
      DAST._IExpression _1663_rExpr = _let_tmp_rhs54.dtor_right;
      DAST.Format._IBinaryOpFormat _1664_format = _let_tmp_rhs54.dtor_format2;
      bool _1665_becomesLeftCallsRight;
      DAST._IBinOp _source85 = _1661_op;
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
          _1665_becomesLeftCallsRight = true;
          goto after_match31;
        }
      }
      {
        _1665_becomesLeftCallsRight = false;
      }
    after_match31: ;
      bool _1666_becomesRightCallsLeft;
      DAST._IBinOp _source86 = _1661_op;
      {
        if (_source86.is_In) {
          _1666_becomesRightCallsLeft = true;
          goto after_match32;
        }
      }
      {
        _1666_becomesRightCallsLeft = false;
      }
    after_match32: ;
      bool _1667_becomesCallLeftRight;
      DAST._IBinOp _source87 = _1661_op;
      {
        if (_source87.is_Eq) {
          bool referential0 = _source87.dtor_referential;
          if ((referential0) == (true)) {
            _1667_becomesCallLeftRight = false;
            goto after_match33;
          }
        }
      }
      {
        if (_source87.is_SetMerge) {
          _1667_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_SetSubtraction) {
          _1667_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_SetIntersection) {
          _1667_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_SetDisjoint) {
          _1667_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_MapMerge) {
          _1667_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_MapSubtraction) {
          _1667_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_MultisetMerge) {
          _1667_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_MultisetSubtraction) {
          _1667_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_MultisetIntersection) {
          _1667_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_MultisetDisjoint) {
          _1667_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source87.is_Concat) {
          _1667_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        _1667_becomesCallLeftRight = false;
      }
    after_match33: ;
      DCOMP._IOwnership _1668_expectedLeftOwnership;
      if (_1665_becomesLeftCallsRight) {
        _1668_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipAutoBorrowed();
      } else if ((_1666_becomesRightCallsLeft) || (_1667_becomesCallLeftRight)) {
        _1668_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        _1668_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipOwned();
      }
      DCOMP._IOwnership _1669_expectedRightOwnership;
      if ((_1665_becomesLeftCallsRight) || (_1667_becomesCallLeftRight)) {
        _1669_expectedRightOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else if (_1666_becomesRightCallsLeft) {
        _1669_expectedRightOwnership = DCOMP.Ownership.create_OwnershipAutoBorrowed();
      } else {
        _1669_expectedRightOwnership = DCOMP.Ownership.create_OwnershipOwned();
      }
      RAST._IExpr _1670_left;
      DCOMP._IOwnership _1671___v112;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1672_recIdentsL;
      RAST._IExpr _out222;
      DCOMP._IOwnership _out223;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out224;
      (this).GenExpr(_1662_lExpr, selfIdent, env, _1668_expectedLeftOwnership, out _out222, out _out223, out _out224);
      _1670_left = _out222;
      _1671___v112 = _out223;
      _1672_recIdentsL = _out224;
      RAST._IExpr _1673_right;
      DCOMP._IOwnership _1674___v113;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1675_recIdentsR;
      RAST._IExpr _out225;
      DCOMP._IOwnership _out226;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out227;
      (this).GenExpr(_1663_rExpr, selfIdent, env, _1669_expectedRightOwnership, out _out225, out _out226, out _out227);
      _1673_right = _out225;
      _1674___v113 = _out226;
      _1675_recIdentsR = _out227;
      DAST._IBinOp _source88 = _1661_op;
      {
        if (_source88.is_In) {
          {
            r = ((_1673_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1670_left);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_SeqProperPrefix) {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1670_left, _1673_right, _1664_format);
          goto after_match34;
        }
      }
      {
        if (_source88.is_SeqPrefix) {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1670_left, _1673_right, _1664_format);
          goto after_match34;
        }
      }
      {
        if (_source88.is_SetMerge) {
          {
            r = ((_1670_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1673_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_SetSubtraction) {
          {
            r = ((_1670_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1673_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_SetIntersection) {
          {
            r = ((_1670_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1673_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_Subset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1670_left, _1673_right, _1664_format);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_ProperSubset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1670_left, _1673_right, _1664_format);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_SetDisjoint) {
          {
            r = ((_1670_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1673_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_MapMerge) {
          {
            r = ((_1670_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1673_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_MapSubtraction) {
          {
            r = ((_1670_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1673_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_MultisetMerge) {
          {
            r = ((_1670_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1673_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_MultisetSubtraction) {
          {
            r = ((_1670_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1673_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_MultisetIntersection) {
          {
            r = ((_1670_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1673_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_Submultiset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1670_left, _1673_right, _1664_format);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_ProperSubmultiset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1670_left, _1673_right, _1664_format);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_MultisetDisjoint) {
          {
            r = ((_1670_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1673_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source88.is_Concat) {
          {
            r = ((_1670_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1673_right);
          }
          goto after_match34;
        }
      }
      {
        {
          if ((DCOMP.COMP.OpTable).Contains(_1661_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1661_op), _1670_left, _1673_right, _1664_format);
          } else {
            DAST._IBinOp _source89 = _1661_op;
            {
              if (_source89.is_Eq) {
                bool _1676_referential = _source89.dtor_referential;
                {
                  if (_1676_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1670_left, _1673_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_1663_rExpr).is_SeqValue) && ((new BigInteger(((_1663_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1670_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1662_lExpr).is_SeqValue) && ((new BigInteger(((_1662_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1673_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1670_left, _1673_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
                goto after_match35;
              }
            }
            {
              if (_source89.is_EuclidianDiv) {
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1670_left, _1673_right));
                }
                goto after_match35;
              }
            }
            {
              if (_source89.is_EuclidianMod) {
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1670_left, _1673_right));
                }
                goto after_match35;
              }
            }
            {
              Dafny.ISequence<Dafny.Rune> _1677_op = _source89.dtor_Passthrough_a0;
              {
                r = RAST.Expr.create_BinaryOp(_1677_op, _1670_left, _1673_right, _1664_format);
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
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1672_recIdentsL, _1675_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _1678_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _1679_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _1680_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _1680_toTpe;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1681_path = _let_tmp_rhs57.dtor_path;
      Dafny.ISequence<DAST._IType> _1682_typeArgs = _let_tmp_rhs57.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs58 = _let_tmp_rhs57.dtor_kind;
      DAST._IType _1683_b = _let_tmp_rhs58.dtor_baseType;
      DAST._INewtypeRange _1684_range = _let_tmp_rhs58.dtor_range;
      bool _1685_erase = _let_tmp_rhs58.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1686___v115 = _let_tmp_rhs57.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1687___v116 = _let_tmp_rhs57.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1688___v117 = _let_tmp_rhs57.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1689_nativeToType;
      _1689_nativeToType = DCOMP.COMP.NewtypeToRustType(_1683_b, _1684_range);
      if (object.Equals(_1679_fromTpe, _1683_b)) {
        RAST._IExpr _1690_recursiveGen;
        DCOMP._IOwnership _1691_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1692_recIdents;
        RAST._IExpr _out230;
        DCOMP._IOwnership _out231;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out232;
        (this).GenExpr(_1678_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out230, out _out231, out _out232);
        _1690_recursiveGen = _out230;
        _1691_recOwned = _out231;
        _1692_recIdents = _out232;
        readIdents = _1692_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source90 = _1689_nativeToType;
        {
          if (_source90.is_Some) {
            RAST._IType _1693_v = _source90.dtor_value;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1690_recursiveGen, RAST.Expr.create_ExprFromType(_1693_v)));
            RAST._IExpr _out233;
            DCOMP._IOwnership _out234;
            (this).FromOwned(r, expectedOwnership, out _out233, out _out234);
            r = _out233;
            resultingOwnership = _out234;
            goto after_match36;
          }
        }
        {
          if (_1685_erase) {
            r = _1690_recursiveGen;
          } else {
            RAST._IType _1694_rhsType;
            RAST._IType _out235;
            _out235 = (this).GenType(_1680_toTpe, DCOMP.GenTypeContext.InBinding());
            _1694_rhsType = _out235;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1694_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1690_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out236;
          DCOMP._IOwnership _out237;
          (this).FromOwnership(r, _1691_recOwned, expectedOwnership, out _out236, out _out237);
          r = _out236;
          resultingOwnership = _out237;
        }
      after_match36: ;
      } else {
        if ((_1689_nativeToType).is_Some) {
          DAST._IType _source91 = _1679_fromTpe;
          {
            if (_source91.is_UserDefined) {
              DAST._IResolvedType resolved1 = _source91.dtor_resolved;
              DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
              if (kind1.is_Newtype) {
                DAST._IType _1695_b0 = kind1.dtor_baseType;
                DAST._INewtypeRange _1696_range0 = kind1.dtor_range;
                bool _1697_erase0 = kind1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1698_attributes0 = resolved1.dtor_attributes;
                {
                  Std.Wrappers._IOption<RAST._IType> _1699_nativeFromType;
                  _1699_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1695_b0, _1696_range0);
                  if ((_1699_nativeFromType).is_Some) {
                    RAST._IExpr _1700_recursiveGen;
                    DCOMP._IOwnership _1701_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1702_recIdents;
                    RAST._IExpr _out238;
                    DCOMP._IOwnership _out239;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out240;
                    (this).GenExpr(_1678_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out238, out _out239, out _out240);
                    _1700_recursiveGen = _out238;
                    _1701_recOwned = _out239;
                    _1702_recIdents = _out240;
                    RAST._IExpr _out241;
                    DCOMP._IOwnership _out242;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_1700_recursiveGen, (_1689_nativeToType).dtor_value), _1701_recOwned, expectedOwnership, out _out241, out _out242);
                    r = _out241;
                    resultingOwnership = _out242;
                    readIdents = _1702_recIdents;
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
          if (object.Equals(_1679_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1703_recursiveGen;
            DCOMP._IOwnership _1704_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1705_recIdents;
            RAST._IExpr _out243;
            DCOMP._IOwnership _out244;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out245;
            (this).GenExpr(_1678_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out243, out _out244, out _out245);
            _1703_recursiveGen = _out243;
            _1704_recOwned = _out244;
            _1705_recIdents = _out245;
            RAST._IExpr _out246;
            DCOMP._IOwnership _out247;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_1703_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1689_nativeToType).dtor_value), _1704_recOwned, expectedOwnership, out _out246, out _out247);
            r = _out246;
            resultingOwnership = _out247;
            readIdents = _1705_recIdents;
            return ;
          }
        }
        RAST._IExpr _out248;
        DCOMP._IOwnership _out249;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out250;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1678_expr, _1679_fromTpe, _1683_b), _1683_b, _1680_toTpe), selfIdent, env, expectedOwnership, out _out248, out _out249, out _out250);
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
      DAST._IExpression _1706_expr = _let_tmp_rhs59.dtor_value;
      DAST._IType _1707_fromTpe = _let_tmp_rhs59.dtor_from;
      DAST._IType _1708_toTpe = _let_tmp_rhs59.dtor_typ;
      DAST._IType _let_tmp_rhs60 = _1707_fromTpe;
      DAST._IResolvedType _let_tmp_rhs61 = _let_tmp_rhs60.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1709___v123 = _let_tmp_rhs61.dtor_path;
      Dafny.ISequence<DAST._IType> _1710___v124 = _let_tmp_rhs61.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs62 = _let_tmp_rhs61.dtor_kind;
      DAST._IType _1711_b = _let_tmp_rhs62.dtor_baseType;
      DAST._INewtypeRange _1712_range = _let_tmp_rhs62.dtor_range;
      bool _1713_erase = _let_tmp_rhs62.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1714_attributes = _let_tmp_rhs61.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1715___v125 = _let_tmp_rhs61.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1716___v126 = _let_tmp_rhs61.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1717_nativeFromType;
      _1717_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1711_b, _1712_range);
      if (object.Equals(_1711_b, _1708_toTpe)) {
        RAST._IExpr _1718_recursiveGen;
        DCOMP._IOwnership _1719_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1720_recIdents;
        RAST._IExpr _out251;
        DCOMP._IOwnership _out252;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out253;
        (this).GenExpr(_1706_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out251, out _out252, out _out253);
        _1718_recursiveGen = _out251;
        _1719_recOwned = _out252;
        _1720_recIdents = _out253;
        readIdents = _1720_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source92 = _1717_nativeFromType;
        {
          if (_source92.is_Some) {
            RAST._IType _1721_v = _source92.dtor_value;
            RAST._IType _1722_toTpeRust;
            RAST._IType _out254;
            _out254 = (this).GenType(_1708_toTpe, DCOMP.GenTypeContext.@default());
            _1722_toTpeRust = _out254;
            r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1722_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1718_recursiveGen));
            RAST._IExpr _out255;
            DCOMP._IOwnership _out256;
            (this).FromOwned(r, expectedOwnership, out _out255, out _out256);
            r = _out255;
            resultingOwnership = _out256;
            goto after_match38;
          }
        }
        {
          if (_1713_erase) {
            r = _1718_recursiveGen;
          } else {
            r = (_1718_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out257;
          DCOMP._IOwnership _out258;
          (this).FromOwnership(r, _1719_recOwned, expectedOwnership, out _out257, out _out258);
          r = _out257;
          resultingOwnership = _out258;
        }
      after_match38: ;
      } else {
        if ((_1717_nativeFromType).is_Some) {
          if (object.Equals(_1708_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1723_recursiveGen;
            DCOMP._IOwnership _1724_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1725_recIdents;
            RAST._IExpr _out259;
            DCOMP._IOwnership _out260;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out261;
            (this).GenExpr(_1706_expr, selfIdent, env, expectedOwnership, out _out259, out _out260, out _out261);
            _1723_recursiveGen = _out259;
            _1724_recOwned = _out260;
            _1725_recIdents = _out261;
            RAST._IExpr _out262;
            DCOMP._IOwnership _out263;
            (this).FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1723_recursiveGen, (this).DafnyCharUnderlying)), _1724_recOwned, expectedOwnership, out _out262, out _out263);
            r = _out262;
            resultingOwnership = _out263;
            readIdents = _1725_recIdents;
            return ;
          }
        }
        RAST._IExpr _out264;
        DCOMP._IOwnership _out265;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out266;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1706_expr, _1707_fromTpe, _1711_b), _1711_b, _1708_toTpe), selfIdent, env, expectedOwnership, out _out264, out _out265, out _out266);
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
        Std.Wrappers._IResult<__T, __E> _1726_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_1726_valueOrError0).IsFailure()) {
          return (_1726_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1727_head = (_1726_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _1728_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_1728_valueOrError1).IsFailure()) {
            return (_1728_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _1729_tail = (_1728_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1727_head), _1729_tail));
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
          RAST._IType _1730_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          RAST._IType _1731_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel((this).upcast)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1730_fromTpeUnderlying, _1731_toTpeUnderlying))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1732_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_1732_valueOrError0).IsFailure()) {
          return (_1732_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1733_lambda = (_1732_valueOrError0).Extract();
          if ((fromType).is_Arrow) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(_1733_lambda);
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).Apply1(_1733_lambda));
          }
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1734_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim12 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr12 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
          for (int i12 = 0; i12 < dim12; i12++) {
            var _1735_i = (BigInteger) i12;
            arr12[(int)(_1735_i)] = (this).UpcastConversionLambda((((fromType).dtor_resolved).dtor_typeArgs).Select(_1735_i), ((fromTpe).dtor_arguments).Select(_1735_i), (((toType).dtor_resolved).dtor_typeArgs).Select(_1735_i), ((toTpe).dtor_arguments).Select(_1735_i), typeParams);
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr12);
        }))());
        if ((_1734_valueOrError1).IsFailure()) {
          return (_1734_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _1736_lambdas = (_1734_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim13 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr13 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim13, "array size exceeds memory limit")];
  for (int i13 = 0; i13 < dim13; i13++) {
    var _1737_i = (BigInteger) i13;
    arr13[(int)(_1737_i)] = ((fromTpe).dtor_arguments).Select(_1737_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr13);
}))())).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_1736_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _1738_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _1739_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _1740_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _1741_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1742_valueOrError2 = (this).UpcastConversionLambda(_1740_newFromType, _1738_newFromTpe, _1741_newToType, _1739_newToTpe, typeParams);
        if ((_1742_valueOrError2).IsFailure()) {
          return (_1742_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1743_coerceArg = (_1742_valueOrError2).Extract();
          RAST._IExpr _1744_collectionType = (RAST.__default.dafny__runtime).MSel(((fromTpe).dtor_baseName).dtor_name);
          RAST._IExpr _1745_baseType = (((((fromTpe).dtor_baseName).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? ((_1744_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((fromTpe).dtor_arguments).Select(BigInteger.Zero), _1738_newFromTpe))) : ((_1744_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1738_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_1745_baseType).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_1743_coerceArg));
        }
      } else if ((((((((((fromTpe).is_DynType) && (((fromTpe).dtor_underlying).is_FnType)) && ((toTpe).is_DynType)) && (((toTpe).dtor_underlying).is_FnType)) && ((((fromTpe).dtor_underlying).dtor_arguments).Equals(((toTpe).dtor_underlying).dtor_arguments))) && ((fromType).is_Arrow)) && ((toType).is_Arrow)) && ((new BigInteger((((fromTpe).dtor_underlying).dtor_arguments).Count)) == (BigInteger.One))) && (((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).is_Borrowed)) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1746_valueOrError3 = (this).UpcastConversionLambda((fromType).dtor_result, ((fromTpe).dtor_underlying).dtor_returnType, (toType).dtor_result, ((toTpe).dtor_underlying).dtor_returnType, typeParams);
        if ((_1746_valueOrError3).IsFailure()) {
          return (_1746_valueOrError3).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1747_lambda = (_1746_valueOrError3).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn1_coerce"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying, ((fromTpe).dtor_underlying).dtor_returnType, ((toTpe).dtor_underlying).dtor_returnType))).Apply1(_1747_lambda));
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
      DAST._IExpression _1748_expr = _let_tmp_rhs63.dtor_value;
      DAST._IType _1749_fromTpe = _let_tmp_rhs63.dtor_from;
      DAST._IType _1750_toTpe = _let_tmp_rhs63.dtor_typ;
      RAST._IType _1751_fromTpeGen;
      RAST._IType _out267;
      _out267 = (this).GenType(_1749_fromTpe, DCOMP.GenTypeContext.InBinding());
      _1751_fromTpeGen = _out267;
      RAST._IType _1752_toTpeGen;
      RAST._IType _out268;
      _out268 = (this).GenType(_1750_toTpe, DCOMP.GenTypeContext.InBinding());
      _1752_toTpeGen = _out268;
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1753_upcastConverter;
      _1753_upcastConverter = (this).UpcastConversionLambda(_1749_fromTpe, _1751_fromTpeGen, _1750_toTpe, _1752_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_1753_upcastConverter).is_Success) {
        RAST._IExpr _1754_conversionLambda;
        _1754_conversionLambda = (_1753_upcastConverter).dtor_value;
        RAST._IExpr _1755_recursiveGen;
        DCOMP._IOwnership _1756_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1757_recIdents;
        RAST._IExpr _out269;
        DCOMP._IOwnership _out270;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out271;
        (this).GenExpr(_1748_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out269, out _out270, out _out271);
        _1755_recursiveGen = _out269;
        _1756_recOwned = _out270;
        _1757_recIdents = _out271;
        readIdents = _1757_recIdents;
        r = (_1754_conversionLambda).Apply1(_1755_recursiveGen);
        RAST._IExpr _out272;
        DCOMP._IOwnership _out273;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out272, out _out273);
        r = _out272;
        resultingOwnership = _out273;
      } else if ((this).IsDowncastConversion(_1751_fromTpeGen, _1752_toTpeGen)) {
        RAST._IExpr _1758_recursiveGen;
        DCOMP._IOwnership _1759_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1760_recIdents;
        RAST._IExpr _out274;
        DCOMP._IOwnership _out275;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out276;
        (this).GenExpr(_1748_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out274, out _out275, out _out276);
        _1758_recursiveGen = _out274;
        _1759_recOwned = _out275;
        _1760_recIdents = _out276;
        readIdents = _1760_recIdents;
        _1752_toTpeGen = (_1752_toTpeGen).ObjectOrPointerUnderlying();
        r = ((RAST.__default.dafny__runtime).MSel((this).downcast)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1758_recursiveGen, RAST.Expr.create_ExprFromType(_1752_toTpeGen)));
        RAST._IExpr _out277;
        DCOMP._IOwnership _out278;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out277, out _out278);
        r = _out277;
        resultingOwnership = _out278;
      } else {
        RAST._IExpr _1761_recursiveGen;
        DCOMP._IOwnership _1762_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1763_recIdents;
        RAST._IExpr _out279;
        DCOMP._IOwnership _out280;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out281;
        (this).GenExpr(_1748_expr, selfIdent, env, expectedOwnership, out _out279, out _out280, out _out281);
        _1761_recursiveGen = _out279;
        _1762_recOwned = _out280;
        _1763_recIdents = _out281;
        readIdents = _1763_recIdents;
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _let_tmp_rhs64 = _1753_upcastConverter;
        _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>> _let_tmp_rhs65 = _let_tmp_rhs64.dtor_error;
        DAST._IType _1764_fromType = _let_tmp_rhs65.dtor__0;
        RAST._IType _1765_fromTpeGen = _let_tmp_rhs65.dtor__1;
        DAST._IType _1766_toType = _let_tmp_rhs65.dtor__2;
        RAST._IType _1767_toTpeGen = _let_tmp_rhs65.dtor__3;
        Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1768_m = _let_tmp_rhs65.dtor__4;
        Dafny.ISequence<Dafny.Rune> _1769_msg;
        _1769_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1765_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1767_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1769_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1761_recursiveGen)._ToString(DCOMP.__default.IND), _1769_msg));
        RAST._IExpr _out282;
        DCOMP._IOwnership _out283;
        (this).FromOwnership(r, _1762_recOwned, expectedOwnership, out _out282, out _out283);
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
      DAST._IExpression _1770_expr = _let_tmp_rhs66.dtor_value;
      DAST._IType _1771_fromTpe = _let_tmp_rhs66.dtor_from;
      DAST._IType _1772_toTpe = _let_tmp_rhs66.dtor_typ;
      if (object.Equals(_1771_fromTpe, _1772_toTpe)) {
        RAST._IExpr _1773_recursiveGen;
        DCOMP._IOwnership _1774_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1775_recIdents;
        RAST._IExpr _out284;
        DCOMP._IOwnership _out285;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out286;
        (this).GenExpr(_1770_expr, selfIdent, env, expectedOwnership, out _out284, out _out285, out _out286);
        _1773_recursiveGen = _out284;
        _1774_recOwned = _out285;
        _1775_recIdents = _out286;
        r = _1773_recursiveGen;
        RAST._IExpr _out287;
        DCOMP._IOwnership _out288;
        (this).FromOwnership(r, _1774_recOwned, expectedOwnership, out _out287, out _out288);
        r = _out287;
        resultingOwnership = _out288;
        readIdents = _1775_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source93 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1771_fromTpe, _1772_toTpe);
        {
          DAST._IType _10 = _source93.dtor__1;
          if (_10.is_UserDefined) {
            DAST._IResolvedType resolved2 = _10.dtor_resolved;
            DAST._IResolvedTypeBase kind2 = resolved2.dtor_kind;
            if (kind2.is_Newtype) {
              DAST._IType _1776_b = kind2.dtor_baseType;
              DAST._INewtypeRange _1777_range = kind2.dtor_range;
              bool _1778_erase = kind2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1779_attributes = resolved2.dtor_attributes;
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
              DAST._IType _1780_b = kind3.dtor_baseType;
              DAST._INewtypeRange _1781_range = kind3.dtor_range;
              bool _1782_erase = kind3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1783_attributes = resolved3.dtor_attributes;
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
                    RAST._IExpr _1784_recursiveGen;
                    DCOMP._IOwnership _1785___v137;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1786_recIdents;
                    RAST._IExpr _out295;
                    DCOMP._IOwnership _out296;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out297;
                    (this).GenExpr(_1770_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out295, out _out296, out _out297);
                    _1784_recursiveGen = _out295;
                    _1785___v137 = _out296;
                    _1786_recIdents = _out297;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1784_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out298;
                    DCOMP._IOwnership _out299;
                    (this).FromOwned(r, expectedOwnership, out _out298, out _out299);
                    r = _out298;
                    resultingOwnership = _out299;
                    readIdents = _1786_recIdents;
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
                    RAST._IExpr _1787_recursiveGen;
                    DCOMP._IOwnership _1788___v138;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1789_recIdents;
                    RAST._IExpr _out300;
                    DCOMP._IOwnership _out301;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out302;
                    (this).GenExpr(_1770_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out300, out _out301, out _out302);
                    _1787_recursiveGen = _out300;
                    _1788___v138 = _out301;
                    _1789_recIdents = _out302;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1787_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out303;
                    DCOMP._IOwnership _out304;
                    (this).FromOwned(r, expectedOwnership, out _out303, out _out304);
                    r = _out303;
                    resultingOwnership = _out304;
                    readIdents = _1789_recIdents;
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
                  RAST._IType _1790_rhsType;
                  RAST._IType _out305;
                  _out305 = (this).GenType(_1772_toTpe, DCOMP.GenTypeContext.InBinding());
                  _1790_rhsType = _out305;
                  RAST._IExpr _1791_recursiveGen;
                  DCOMP._IOwnership _1792___v140;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1793_recIdents;
                  RAST._IExpr _out306;
                  DCOMP._IOwnership _out307;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out308;
                  (this).GenExpr(_1770_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out306, out _out307, out _out308);
                  _1791_recursiveGen = _out306;
                  _1792___v140 = _out307;
                  _1793_recIdents = _out308;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1790_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1791_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out309;
                  DCOMP._IOwnership _out310;
                  (this).FromOwned(r, expectedOwnership, out _out309, out _out310);
                  r = _out309;
                  resultingOwnership = _out310;
                  readIdents = _1793_recIdents;
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
                  RAST._IType _1794_rhsType;
                  RAST._IType _out311;
                  _out311 = (this).GenType(_1771_fromTpe, DCOMP.GenTypeContext.InBinding());
                  _1794_rhsType = _out311;
                  RAST._IExpr _1795_recursiveGen;
                  DCOMP._IOwnership _1796___v142;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1797_recIdents;
                  RAST._IExpr _out312;
                  DCOMP._IOwnership _out313;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out314;
                  (this).GenExpr(_1770_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out312, out _out313, out _out314);
                  _1795_recursiveGen = _out312;
                  _1796___v142 = _out313;
                  _1797_recIdents = _out314;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_1795_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out315;
                  DCOMP._IOwnership _out316;
                  (this).FromOwned(r, expectedOwnership, out _out315, out _out316);
                  r = _out315;
                  resultingOwnership = _out316;
                  readIdents = _1797_recIdents;
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
                    RAST._IType _1798_rhsType;
                    RAST._IType _out317;
                    _out317 = (this).GenType(_1772_toTpe, DCOMP.GenTypeContext.InBinding());
                    _1798_rhsType = _out317;
                    RAST._IExpr _1799_recursiveGen;
                    DCOMP._IOwnership _1800___v143;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1801_recIdents;
                    RAST._IExpr _out318;
                    DCOMP._IOwnership _out319;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out320;
                    (this).GenExpr(_1770_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out318, out _out319, out _out320);
                    _1799_recursiveGen = _out318;
                    _1800___v143 = _out319;
                    _1801_recIdents = _out320;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1799_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out321;
                    DCOMP._IOwnership _out322;
                    (this).FromOwned(r, expectedOwnership, out _out321, out _out322);
                    r = _out321;
                    resultingOwnership = _out322;
                    readIdents = _1801_recIdents;
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
                    RAST._IType _1802_rhsType;
                    RAST._IType _out323;
                    _out323 = (this).GenType(_1771_fromTpe, DCOMP.GenTypeContext.InBinding());
                    _1802_rhsType = _out323;
                    RAST._IExpr _1803_recursiveGen;
                    DCOMP._IOwnership _1804___v144;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1805_recIdents;
                    RAST._IExpr _out324;
                    DCOMP._IOwnership _out325;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out326;
                    (this).GenExpr(_1770_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out324, out _out325, out _out326);
                    _1803_recursiveGen = _out324;
                    _1804___v144 = _out325;
                    _1805_recIdents = _out326;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1803_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out327;
                    DCOMP._IOwnership _out328;
                    (this).FromOwned(r, expectedOwnership, out _out327, out _out328);
                    r = _out327;
                    resultingOwnership = _out328;
                    readIdents = _1805_recIdents;
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
                RAST._IExpr _1806_recursiveGen;
                DCOMP._IOwnership _1807___v147;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1808_recIdents;
                RAST._IExpr _out329;
                DCOMP._IOwnership _out330;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
                (this).GenExpr(_1770_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out329, out _out330, out _out331);
                _1806_recursiveGen = _out329;
                _1807___v147 = _out330;
                _1808_recIdents = _out331;
                RAST._IType _1809_toTpeGen;
                RAST._IType _out332;
                _out332 = (this).GenType(_1772_toTpe, DCOMP.GenTypeContext.InBinding());
                _1809_toTpeGen = _out332;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1806_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1809_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out333;
                DCOMP._IOwnership _out334;
                (this).FromOwned(r, expectedOwnership, out _out333, out _out334);
                r = _out333;
                resultingOwnership = _out334;
                readIdents = _1808_recIdents;
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
      Std.Wrappers._IOption<RAST._IType> _1810_tpe;
      _1810_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1811_placeboOpt;
      if ((_1810_tpe).is_Some) {
        _1811_placeboOpt = ((_1810_tpe).dtor_value).ExtractMaybePlacebo();
      } else {
        _1811_placeboOpt = Std.Wrappers.Option<RAST._IType>.create_None();
      }
      bool _1812_currentlyBorrowed;
      _1812_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1813_noNeedOfClone;
      _1813_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1811_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _1812_currentlyBorrowed = false;
        _1813_noNeedOfClone = true;
        _1810_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_1811_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        if (_1812_currentlyBorrowed) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        } else {
          resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
        }
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_1810_tpe).is_Some) && (((_1810_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _1814_needObjectFromRef;
        _1814_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source94 = (selfIdent).dtor_dafnyType;
          {
            if (_source94.is_UserDefined) {
              DAST._IResolvedType resolved4 = _source94.dtor_resolved;
              DAST._IResolvedTypeBase _1815_base = resolved4.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _1816_attributes = resolved4.dtor_attributes;
              return ((_1815_base).is_Class) || ((_1815_base).is_Trait);
            }
          }
          {
            return false;
          }
        }))());
        if (_1814_needObjectFromRef) {
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_1813_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1813_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1812_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_1810_tpe).is_Some) && (((_1810_tpe).dtor_value).IsPointer())) {
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
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_1817_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_1817_attributes).UniqueElements, false, (((_exists_var_1) => {
        DAST._IAttribute _1818_attribute = (DAST._IAttribute)_exists_var_1;
        return ((_1817_attributes).Contains(_1818_attribute)) && ((((_1818_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_1818_attribute).dtor_args).Count)) == (new BigInteger(2))));
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
      for (BigInteger _1819_i = BigInteger.Zero; _1819_i < _hi37; _1819_i++) {
        DCOMP._IOwnership _1820_argOwnership;
        _1820_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if (((name).is_CallName) && ((_1819_i) < (new BigInteger((((name).dtor_signature)).Count)))) {
          RAST._IType _1821_tpe;
          RAST._IType _out338;
          _out338 = (this).GenType(((((name).dtor_signature)).Select(_1819_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _1821_tpe = _out338;
          if ((_1821_tpe).CanReadWithoutClone()) {
            _1820_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _1822_argExpr;
        DCOMP._IOwnership _1823___v154;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1824_argIdents;
        RAST._IExpr _out339;
        DCOMP._IOwnership _out340;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out341;
        (this).GenExpr((args).Select(_1819_i), selfIdent, env, _1820_argOwnership, out _out339, out _out340, out _out341);
        _1822_argExpr = _out339;
        _1823___v154 = _out340;
        _1824_argIdents = _out341;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1822_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1824_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi38 = new BigInteger((typeArgs).Count);
      for (BigInteger _1825_typeI = BigInteger.Zero; _1825_typeI < _hi38; _1825_typeI++) {
        RAST._IType _1826_typeExpr;
        RAST._IType _out342;
        _out342 = (this).GenType((typeArgs).Select(_1825_typeI), DCOMP.GenTypeContext.@default());
        _1826_typeExpr = _out342;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1826_typeExpr));
      }
      DAST._ICallName _source95 = name;
      {
        if (_source95.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _1827_nameIdent = _source95.dtor_name;
          Std.Wrappers._IOption<DAST._IType> onType1 = _source95.dtor_onType;
          if (onType1.is_Some) {
            DAST._IType value10 = onType1.dtor_value;
            if (value10.is_UserDefined) {
              DAST._IResolvedType _1828_resolvedType = value10.dtor_resolved;
              if ((((_1828_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_1829_resolvedType, _1830_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(((_1829_resolvedType).dtor_properMethods).UniqueElements, true, (((_forall_var_8) => {
                Dafny.ISequence<Dafny.Rune> _1831_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_8;
                return !(((_1829_resolvedType).dtor_properMethods).Contains(_1831_m)) || (!object.Equals((_1831_m), _1830_nameIdent));
              }))))(_1828_resolvedType, _1827_nameIdent))) {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_1828_resolvedType, (_1827_nameIdent)), _1828_resolvedType));
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
          Dafny.ISequence<Dafny.Rune> _1832_name = _source96.dtor_name;
          {
            RAST._IExpr _out346;
            DCOMP._IOwnership _out347;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out348;
            (this).GenIdent(DCOMP.__default.escapeName(_1832_name), selfIdent, env, expectedOwnership, out _out346, out _out347, out _out348);
            r = _out346;
            resultingOwnership = _out347;
            readIdents = _out348;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1833_path = _source96.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _1834_typeArgs = _source96.dtor_typeArgs;
          {
            RAST._IExpr _out349;
            _out349 = DCOMP.COMP.GenPathExpr(_1833_path);
            r = _out349;
            if ((new BigInteger((_1834_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1835_typeExprs;
              _1835_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi39 = new BigInteger((_1834_typeArgs).Count);
              for (BigInteger _1836_i = BigInteger.Zero; _1836_i < _hi39; _1836_i++) {
                RAST._IType _1837_typeExpr;
                RAST._IType _out350;
                _out350 = (this).GenType((_1834_typeArgs).Select(_1836_i), DCOMP.GenTypeContext.@default());
                _1837_typeExpr = _out350;
                _1835_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1835_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1837_typeExpr));
              }
              r = (r).ApplyType(_1835_typeExprs);
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
          DAST._IType _1838_typ = _source96.dtor_typ;
          {
            RAST._IType _1839_typExpr;
            RAST._IType _out353;
            _out353 = (this).GenType(_1838_typ, DCOMP.GenTypeContext.@default());
            _1839_typExpr = _out353;
            if ((_1839_typExpr).IsObjectOrPointer()) {
              r = (_1839_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1839_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
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
          Dafny.ISequence<DAST._IExpression> _1840_values = _source96.dtor_Tuple_a0;
          {
            Dafny.ISequence<RAST._IExpr> _1841_exprs;
            _1841_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi40 = new BigInteger((_1840_values).Count);
            for (BigInteger _1842_i = BigInteger.Zero; _1842_i < _hi40; _1842_i++) {
              RAST._IExpr _1843_recursiveGen;
              DCOMP._IOwnership _1844___v159;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1845_recIdents;
              RAST._IExpr _out356;
              DCOMP._IOwnership _out357;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out358;
              (this).GenExpr((_1840_values).Select(_1842_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out356, out _out357, out _out358);
              _1843_recursiveGen = _out356;
              _1844___v159 = _out357;
              _1845_recIdents = _out358;
              _1841_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1841_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1843_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1845_recIdents);
            }
            if ((new BigInteger((_1840_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) {
              r = RAST.Expr.create_Tuple(_1841_exprs);
            } else {
              r = RAST.__default.SystemTuple(_1841_exprs);
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
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1846_path = _source96.dtor_path;
          Dafny.ISequence<DAST._IType> _1847_typeArgs = _source96.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1848_args = _source96.dtor_args;
          {
            RAST._IExpr _out361;
            _out361 = DCOMP.COMP.GenPathExpr(_1846_path);
            r = _out361;
            if ((new BigInteger((_1847_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1849_typeExprs;
              _1849_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi41 = new BigInteger((_1847_typeArgs).Count);
              for (BigInteger _1850_i = BigInteger.Zero; _1850_i < _hi41; _1850_i++) {
                RAST._IType _1851_typeExpr;
                RAST._IType _out362;
                _out362 = (this).GenType((_1847_typeArgs).Select(_1850_i), DCOMP.GenTypeContext.@default());
                _1851_typeExpr = _out362;
                _1849_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1849_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1851_typeExpr));
              }
              r = (r).ApplyType(_1849_typeExprs);
            }
            r = (r).MSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1852_arguments;
            _1852_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi42 = new BigInteger((_1848_args).Count);
            for (BigInteger _1853_i = BigInteger.Zero; _1853_i < _hi42; _1853_i++) {
              RAST._IExpr _1854_recursiveGen;
              DCOMP._IOwnership _1855___v160;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1856_recIdents;
              RAST._IExpr _out363;
              DCOMP._IOwnership _out364;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out365;
              (this).GenExpr((_1848_args).Select(_1853_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out363, out _out364, out _out365);
              _1854_recursiveGen = _out363;
              _1855___v160 = _out364;
              _1856_recIdents = _out365;
              _1852_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1852_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1854_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1856_recIdents);
            }
            r = (r).Apply(_1852_arguments);
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
          Dafny.ISequence<DAST._IExpression> _1857_dims = _source96.dtor_dims;
          DAST._IType _1858_typ = _source96.dtor_typ;
          {
            if ((new BigInteger(16)) < (new BigInteger((_1857_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _1859_msg;
              _1859_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1859_msg);
              }
              r = RAST.Expr.create_RawExpr(_1859_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _1860_typeGen;
              RAST._IType _out368;
              _out368 = (this).GenType(_1858_typ, DCOMP.GenTypeContext.@default());
              _1860_typeGen = _out368;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _1861_dimExprs;
              _1861_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi43 = new BigInteger((_1857_dims).Count);
              for (BigInteger _1862_i = BigInteger.Zero; _1862_i < _hi43; _1862_i++) {
                RAST._IExpr _1863_recursiveGen;
                DCOMP._IOwnership _1864___v161;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1865_recIdents;
                RAST._IExpr _out369;
                DCOMP._IOwnership _out370;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out371;
                (this).GenExpr((_1857_dims).Select(_1862_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out369, out _out370, out _out371);
                _1863_recursiveGen = _out369;
                _1864___v161 = _out370;
                _1865_recIdents = _out371;
                _1861_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1861_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.IntoUsize(_1863_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1865_recIdents);
              }
              if ((new BigInteger((_1857_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _1866_class__name;
                _1866_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_1857_dims).Count)));
                r = ((((RAST.__default.dafny__runtime).MSel(_1866_class__name)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1860_typeGen))).MSel((this).placebos__usize)).Apply(_1861_dimExprs);
              } else {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1860_typeGen))).Apply(_1861_dimExprs);
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
          DAST._IExpression _1867_underlying = _source96.dtor_value;
          {
            RAST._IExpr _1868_recursiveGen;
            DCOMP._IOwnership _1869___v162;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1870_recIdents;
            RAST._IExpr _out374;
            DCOMP._IOwnership _out375;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out376;
            (this).GenExpr(_1867_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out374, out _out375, out _out376);
            _1868_recursiveGen = _out374;
            _1869___v162 = _out375;
            _1870_recIdents = _out376;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(_1868_recursiveGen);
            readIdents = _1870_recIdents;
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
          DAST._IExpression _1871_underlying = _source96.dtor_value;
          DAST._IType _1872_typ = _source96.dtor_typ;
          {
            RAST._IType _1873_tpe;
            RAST._IType _out379;
            _out379 = (this).GenType(_1872_typ, DCOMP.GenTypeContext.@default());
            _1873_tpe = _out379;
            RAST._IExpr _1874_recursiveGen;
            DCOMP._IOwnership _1875___v163;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1876_recIdents;
            RAST._IExpr _out380;
            DCOMP._IOwnership _out381;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out382;
            (this).GenExpr(_1871_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out380, out _out381, out _out382);
            _1874_recursiveGen = _out380;
            _1875___v163 = _out381;
            _1876_recIdents = _out382;
            readIdents = _1876_recIdents;
            if ((_1873_tpe).IsObjectOrPointer()) {
              RAST._IType _1877_t;
              _1877_t = (_1873_tpe).ObjectOrPointerUnderlying();
              if ((_1877_t).is_Array) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).array__construct)).Apply1(_1874_recursiveGen);
              } else if ((_1877_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _1878_c;
                _1878_c = (_1877_t).MultiArrayClass();
                r = (((RAST.__default.dafny__runtime).MSel(_1878_c)).MSel((this).array__construct)).Apply1(_1874_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_1873_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_1873_tpe)._ToString(DCOMP.__default.IND)));
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
          DAST._IResolvedType _1879_datatypeType = _source96.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1880_typeArgs = _source96.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1881_variant = _source96.dtor_variant;
          bool _1882_isCo = _source96.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1883_values = _source96.dtor_contents;
          {
            RAST._IExpr _out385;
            _out385 = DCOMP.COMP.GenPathExpr((_1879_datatypeType).dtor_path);
            r = _out385;
            Dafny.ISequence<RAST._IType> _1884_genTypeArgs;
            _1884_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi44 = new BigInteger((_1880_typeArgs).Count);
            for (BigInteger _1885_i = BigInteger.Zero; _1885_i < _hi44; _1885_i++) {
              RAST._IType _1886_typeExpr;
              RAST._IType _out386;
              _out386 = (this).GenType((_1880_typeArgs).Select(_1885_i), DCOMP.GenTypeContext.@default());
              _1886_typeExpr = _out386;
              _1884_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1884_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1886_typeExpr));
            }
            if ((new BigInteger((_1880_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1884_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1881_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1887_assignments;
            _1887_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi45 = new BigInteger((_1883_values).Count);
            for (BigInteger _1888_i = BigInteger.Zero; _1888_i < _hi45; _1888_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs67 = (_1883_values).Select(_1888_i);
              Dafny.ISequence<Dafny.Rune> _1889_name = _let_tmp_rhs67.dtor__0;
              DAST._IExpression _1890_value = _let_tmp_rhs67.dtor__1;
              if (_1882_isCo) {
                RAST._IExpr _1891_recursiveGen;
                DCOMP._IOwnership _1892___v164;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1893_recIdents;
                RAST._IExpr _out387;
                DCOMP._IOwnership _out388;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out389;
                (this).GenExpr(_1890_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out387, out _out388, out _out389);
                _1891_recursiveGen = _out387;
                _1892___v164 = _out388;
                _1893_recIdents = _out389;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1893_recIdents);
                Dafny.ISequence<Dafny.Rune> _1894_allReadCloned;
                _1894_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1893_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1895_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1893_recIdents).Elements) {
                    _1895_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1893_recIdents).Contains(_1895_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4402)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1894_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1894_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1895_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1895_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1893_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1893_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1895_next));
                }
                Dafny.ISequence<Dafny.Rune> _1896_wasAssigned;
                _1896_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1894_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1891_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1887_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1887_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1889_name), RAST.Expr.create_RawExpr(_1896_wasAssigned))));
              } else {
                RAST._IExpr _1897_recursiveGen;
                DCOMP._IOwnership _1898___v165;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1899_recIdents;
                RAST._IExpr _out390;
                DCOMP._IOwnership _out391;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out392;
                (this).GenExpr(_1890_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out390, out _out391, out _out392);
                _1897_recursiveGen = _out390;
                _1898___v165 = _out391;
                _1899_recIdents = _out392;
                _1887_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1887_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1889_name), _1897_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1899_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1887_assignments);
            if ((this).IsRcWrapped((_1879_datatypeType).dtor_attributes)) {
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
          DAST._IExpression _1900_length = _source96.dtor_length;
          DAST._IExpression _1901_expr = _source96.dtor_elem;
          {
            RAST._IExpr _1902_recursiveGen;
            DCOMP._IOwnership _1903___v169;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1904_recIdents;
            RAST._IExpr _out398;
            DCOMP._IOwnership _out399;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out400;
            (this).GenExpr(_1901_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out398, out _out399, out _out400);
            _1902_recursiveGen = _out398;
            _1903___v169 = _out399;
            _1904_recIdents = _out400;
            RAST._IExpr _1905_lengthGen;
            DCOMP._IOwnership _1906___v170;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1907_lengthIdents;
            RAST._IExpr _out401;
            DCOMP._IOwnership _out402;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
            (this).GenExpr(_1900_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out401, out _out402, out _out403);
            _1905_lengthGen = _out401;
            _1906___v170 = _out402;
            _1907_lengthIdents = _out403;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1902_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1905_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1904_recIdents, _1907_lengthIdents);
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
          Dafny.ISequence<DAST._IExpression> _1908_exprs = _source96.dtor_elements;
          DAST._IType _1909_typ = _source96.dtor_typ;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1910_genTpe;
            RAST._IType _out406;
            _out406 = (this).GenType(_1909_typ, DCOMP.GenTypeContext.@default());
            _1910_genTpe = _out406;
            BigInteger _1911_i;
            _1911_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1912_args;
            _1912_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1911_i) < (new BigInteger((_1908_exprs).Count))) {
              RAST._IExpr _1913_recursiveGen;
              DCOMP._IOwnership _1914___v171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1915_recIdents;
              RAST._IExpr _out407;
              DCOMP._IOwnership _out408;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
              (this).GenExpr((_1908_exprs).Select(_1911_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out407, out _out408, out _out409);
              _1913_recursiveGen = _out407;
              _1914___v171 = _out408;
              _1915_recIdents = _out409;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1915_recIdents);
              _1912_args = Dafny.Sequence<RAST._IExpr>.Concat(_1912_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1913_recursiveGen));
              _1911_i = (_1911_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_1912_args);
            if ((new BigInteger((_1912_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1910_genTpe));
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
          Dafny.ISequence<DAST._IExpression> _1916_exprs = _source96.dtor_elements;
          {
            Dafny.ISequence<RAST._IExpr> _1917_generatedValues;
            _1917_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1918_i;
            _1918_i = BigInteger.Zero;
            while ((_1918_i) < (new BigInteger((_1916_exprs).Count))) {
              RAST._IExpr _1919_recursiveGen;
              DCOMP._IOwnership _1920___v172;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1921_recIdents;
              RAST._IExpr _out412;
              DCOMP._IOwnership _out413;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out414;
              (this).GenExpr((_1916_exprs).Select(_1918_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out412, out _out413, out _out414);
              _1919_recursiveGen = _out412;
              _1920___v172 = _out413;
              _1921_recIdents = _out414;
              _1917_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1917_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1919_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1921_recIdents);
              _1918_i = (_1918_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_1917_generatedValues);
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
          Dafny.ISequence<DAST._IExpression> _1922_exprs = _source96.dtor_elements;
          {
            Dafny.ISequence<RAST._IExpr> _1923_generatedValues;
            _1923_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1924_i;
            _1924_i = BigInteger.Zero;
            while ((_1924_i) < (new BigInteger((_1922_exprs).Count))) {
              RAST._IExpr _1925_recursiveGen;
              DCOMP._IOwnership _1926___v173;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1927_recIdents;
              RAST._IExpr _out417;
              DCOMP._IOwnership _out418;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out419;
              (this).GenExpr((_1922_exprs).Select(_1924_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out417, out _out418, out _out419);
              _1925_recursiveGen = _out417;
              _1926___v173 = _out418;
              _1927_recIdents = _out419;
              _1923_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1923_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1925_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1927_recIdents);
              _1924_i = (_1924_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_1923_generatedValues);
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
          DAST._IExpression _1928_expr = _source96.dtor_ToMultiset_a0;
          {
            RAST._IExpr _1929_recursiveGen;
            DCOMP._IOwnership _1930___v174;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1931_recIdents;
            RAST._IExpr _out422;
            DCOMP._IOwnership _out423;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out424;
            (this).GenExpr(_1928_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out422, out _out423, out _out424);
            _1929_recursiveGen = _out422;
            _1930___v174 = _out423;
            _1931_recIdents = _out424;
            r = ((_1929_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _1931_recIdents;
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
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1932_mapElems = _source96.dtor_mapElems;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1933_generatedValues;
            _1933_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1934_i;
            _1934_i = BigInteger.Zero;
            while ((_1934_i) < (new BigInteger((_1932_mapElems).Count))) {
              RAST._IExpr _1935_recursiveGenKey;
              DCOMP._IOwnership _1936___v175;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1937_recIdentsKey;
              RAST._IExpr _out427;
              DCOMP._IOwnership _out428;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out429;
              (this).GenExpr(((_1932_mapElems).Select(_1934_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out427, out _out428, out _out429);
              _1935_recursiveGenKey = _out427;
              _1936___v175 = _out428;
              _1937_recIdentsKey = _out429;
              RAST._IExpr _1938_recursiveGenValue;
              DCOMP._IOwnership _1939___v176;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1940_recIdentsValue;
              RAST._IExpr _out430;
              DCOMP._IOwnership _out431;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out432;
              (this).GenExpr(((_1932_mapElems).Select(_1934_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out430, out _out431, out _out432);
              _1938_recursiveGenValue = _out430;
              _1939___v176 = _out431;
              _1940_recIdentsValue = _out432;
              _1933_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1933_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1935_recursiveGenKey, _1938_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1937_recIdentsKey), _1940_recIdentsValue);
              _1934_i = (_1934_i) + (BigInteger.One);
            }
            _1934_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1941_arguments;
            _1941_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1934_i) < (new BigInteger((_1933_generatedValues).Count))) {
              RAST._IExpr _1942_genKey;
              _1942_genKey = ((_1933_generatedValues).Select(_1934_i)).dtor__0;
              RAST._IExpr _1943_genValue;
              _1943_genValue = ((_1933_generatedValues).Select(_1934_i)).dtor__1;
              _1941_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1941_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1942_genKey, _1943_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _1934_i = (_1934_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_1941_arguments);
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
          DAST._IExpression _1944_expr = _source96.dtor_expr;
          DAST._IExpression _1945_index = _source96.dtor_indexExpr;
          DAST._IExpression _1946_value = _source96.dtor_value;
          {
            RAST._IExpr _1947_exprR;
            DCOMP._IOwnership _1948___v177;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1949_exprIdents;
            RAST._IExpr _out435;
            DCOMP._IOwnership _out436;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out437;
            (this).GenExpr(_1944_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out435, out _out436, out _out437);
            _1947_exprR = _out435;
            _1948___v177 = _out436;
            _1949_exprIdents = _out437;
            RAST._IExpr _1950_indexR;
            DCOMP._IOwnership _1951_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1952_indexIdents;
            RAST._IExpr _out438;
            DCOMP._IOwnership _out439;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out440;
            (this).GenExpr(_1945_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out438, out _out439, out _out440);
            _1950_indexR = _out438;
            _1951_indexOwnership = _out439;
            _1952_indexIdents = _out440;
            RAST._IExpr _1953_valueR;
            DCOMP._IOwnership _1954_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1955_valueIdents;
            RAST._IExpr _out441;
            DCOMP._IOwnership _out442;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out443;
            (this).GenExpr(_1946_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out441, out _out442, out _out443);
            _1953_valueR = _out441;
            _1954_valueOwnership = _out442;
            _1955_valueIdents = _out443;
            r = ((_1947_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1950_indexR, _1953_valueR));
            RAST._IExpr _out444;
            DCOMP._IOwnership _out445;
            (this).FromOwned(r, expectedOwnership, out _out444, out _out445);
            r = _out444;
            resultingOwnership = _out445;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1949_exprIdents, _1952_indexIdents), _1955_valueIdents);
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_MapUpdate) {
          DAST._IExpression _1956_expr = _source96.dtor_expr;
          DAST._IExpression _1957_index = _source96.dtor_indexExpr;
          DAST._IExpression _1958_value = _source96.dtor_value;
          {
            RAST._IExpr _1959_exprR;
            DCOMP._IOwnership _1960___v178;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1961_exprIdents;
            RAST._IExpr _out446;
            DCOMP._IOwnership _out447;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out448;
            (this).GenExpr(_1956_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out446, out _out447, out _out448);
            _1959_exprR = _out446;
            _1960___v178 = _out447;
            _1961_exprIdents = _out448;
            RAST._IExpr _1962_indexR;
            DCOMP._IOwnership _1963_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1964_indexIdents;
            RAST._IExpr _out449;
            DCOMP._IOwnership _out450;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
            (this).GenExpr(_1957_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out449, out _out450, out _out451);
            _1962_indexR = _out449;
            _1963_indexOwnership = _out450;
            _1964_indexIdents = _out451;
            RAST._IExpr _1965_valueR;
            DCOMP._IOwnership _1966_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1967_valueIdents;
            RAST._IExpr _out452;
            DCOMP._IOwnership _out453;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out454;
            (this).GenExpr(_1958_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out452, out _out453, out _out454);
            _1965_valueR = _out452;
            _1966_valueOwnership = _out453;
            _1967_valueIdents = _out454;
            r = ((_1959_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1962_indexR, _1965_valueR));
            RAST._IExpr _out455;
            DCOMP._IOwnership _out456;
            (this).FromOwned(r, expectedOwnership, out _out455, out _out456);
            r = _out455;
            resultingOwnership = _out456;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1961_exprIdents, _1964_indexIdents), _1967_valueIdents);
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
                Dafny.ISequence<Dafny.Rune> _1968_id = _source97.dtor_rSelfName;
                DAST._IType _1969_dafnyType = _source97.dtor_dafnyType;
                {
                  RAST._IExpr _out457;
                  DCOMP._IOwnership _out458;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out459;
                  (this).GenIdent(_1968_id, selfIdent, env, expectedOwnership, out _out457, out _out458, out _out459);
                  r = _out457;
                  resultingOwnership = _out458;
                  readIdents = _out459;
                }
                goto after_match42;
              }
            }
            {
              DCOMP._ISelfInfo _1970_None = _source97;
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
          DAST._IExpression _1971_cond = _source96.dtor_cond;
          DAST._IExpression _1972_t = _source96.dtor_thn;
          DAST._IExpression _1973_f = _source96.dtor_els;
          {
            RAST._IExpr _1974_cond;
            DCOMP._IOwnership _1975___v179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1976_recIdentsCond;
            RAST._IExpr _out462;
            DCOMP._IOwnership _out463;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out464;
            (this).GenExpr(_1971_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out462, out _out463, out _out464);
            _1974_cond = _out462;
            _1975___v179 = _out463;
            _1976_recIdentsCond = _out464;
            RAST._IExpr _1977_fExpr;
            DCOMP._IOwnership _1978_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1979_recIdentsF;
            RAST._IExpr _out465;
            DCOMP._IOwnership _out466;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out467;
            (this).GenExpr(_1973_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out465, out _out466, out _out467);
            _1977_fExpr = _out465;
            _1978_fOwned = _out466;
            _1979_recIdentsF = _out467;
            RAST._IExpr _1980_tExpr;
            DCOMP._IOwnership _1981___v180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1982_recIdentsT;
            RAST._IExpr _out468;
            DCOMP._IOwnership _out469;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out470;
            (this).GenExpr(_1972_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out468, out _out469, out _out470);
            _1980_tExpr = _out468;
            _1981___v180 = _out469;
            _1982_recIdentsT = _out470;
            r = RAST.Expr.create_IfExpr(_1974_cond, _1980_tExpr, _1977_fExpr);
            RAST._IExpr _out471;
            DCOMP._IOwnership _out472;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out471, out _out472);
            r = _out471;
            resultingOwnership = _out472;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1976_recIdentsCond, _1982_recIdentsT), _1979_recIdentsF);
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source96.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _1983_e = _source96.dtor_expr;
            DAST.Format._IUnaryOpFormat _1984_format = _source96.dtor_format1;
            {
              RAST._IExpr _1985_recursiveGen;
              DCOMP._IOwnership _1986___v181;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1987_recIdents;
              RAST._IExpr _out473;
              DCOMP._IOwnership _out474;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out475;
              (this).GenExpr(_1983_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out473, out _out474, out _out475);
              _1985_recursiveGen = _out473;
              _1986___v181 = _out474;
              _1987_recIdents = _out475;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _1985_recursiveGen, _1984_format);
              RAST._IExpr _out476;
              DCOMP._IOwnership _out477;
              (this).FromOwned(r, expectedOwnership, out _out476, out _out477);
              r = _out476;
              resultingOwnership = _out477;
              readIdents = _1987_recIdents;
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
            DAST._IExpression _1988_e = _source96.dtor_expr;
            DAST.Format._IUnaryOpFormat _1989_format = _source96.dtor_format1;
            {
              RAST._IExpr _1990_recursiveGen;
              DCOMP._IOwnership _1991___v182;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1992_recIdents;
              RAST._IExpr _out478;
              DCOMP._IOwnership _out479;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out480;
              (this).GenExpr(_1988_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out478, out _out479, out _out480);
              _1990_recursiveGen = _out478;
              _1991___v182 = _out479;
              _1992_recIdents = _out480;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _1990_recursiveGen, _1989_format);
              RAST._IExpr _out481;
              DCOMP._IOwnership _out482;
              (this).FromOwned(r, expectedOwnership, out _out481, out _out482);
              r = _out481;
              resultingOwnership = _out482;
              readIdents = _1992_recIdents;
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
            DAST._IExpression _1993_e = _source96.dtor_expr;
            DAST.Format._IUnaryOpFormat _1994_format = _source96.dtor_format1;
            {
              RAST._IExpr _1995_recursiveGen;
              DCOMP._IOwnership _1996_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1997_recIdents;
              RAST._IExpr _out483;
              DCOMP._IOwnership _out484;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out485;
              (this).GenExpr(_1993_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out483, out _out484, out _out485);
              _1995_recursiveGen = _out483;
              _1996_recOwned = _out484;
              _1997_recIdents = _out485;
              r = ((_1995_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out486;
              DCOMP._IOwnership _out487;
              (this).FromOwned(r, expectedOwnership, out _out486, out _out487);
              r = _out486;
              resultingOwnership = _out487;
              readIdents = _1997_recIdents;
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
          DAST._IExpression _1998_expr = _source96.dtor_expr;
          DAST._IType _1999_exprType = _source96.dtor_exprType;
          BigInteger _2000_dim = _source96.dtor_dim;
          bool _2001_native = _source96.dtor_native;
          {
            RAST._IExpr _2002_recursiveGen;
            DCOMP._IOwnership _2003___v187;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2004_recIdents;
            RAST._IExpr _out491;
            DCOMP._IOwnership _out492;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out493;
            (this).GenExpr(_1998_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out491, out _out492, out _out493);
            _2002_recursiveGen = _out491;
            _2003___v187 = _out492;
            _2004_recIdents = _out493;
            RAST._IType _2005_arrayType;
            RAST._IType _out494;
            _out494 = (this).GenType(_1999_exprType, DCOMP.GenTypeContext.@default());
            _2005_arrayType = _out494;
            if (!((_2005_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _2006_msg;
              _2006_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_2005_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2006_msg);
              r = RAST.Expr.create_RawExpr(_2006_msg);
            } else {
              RAST._IType _2007_underlying;
              _2007_underlying = (_2005_arrayType).ObjectOrPointerUnderlying();
              if (((_2000_dim).Sign == 0) && ((_2007_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_2002_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_2000_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_2002_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = ((((this).read__macro).Apply1(_2002_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("length"), Std.Strings.__default.OfNat(_2000_dim)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_usize")))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                }
              }
              if (!(_2001_native)) {
                r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(r);
              }
            }
            RAST._IExpr _out495;
            DCOMP._IOwnership _out496;
            (this).FromOwned(r, expectedOwnership, out _out495, out _out496);
            r = _out495;
            resultingOwnership = _out496;
            readIdents = _2004_recIdents;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_MapKeys) {
          DAST._IExpression _2008_expr = _source96.dtor_expr;
          {
            RAST._IExpr _2009_recursiveGen;
            DCOMP._IOwnership _2010___v188;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2011_recIdents;
            RAST._IExpr _out497;
            DCOMP._IOwnership _out498;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out499;
            (this).GenExpr(_2008_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out497, out _out498, out _out499);
            _2009_recursiveGen = _out497;
            _2010___v188 = _out498;
            _2011_recIdents = _out499;
            readIdents = _2011_recIdents;
            r = ((_2009_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
          DAST._IExpression _2012_expr = _source96.dtor_expr;
          {
            RAST._IExpr _2013_recursiveGen;
            DCOMP._IOwnership _2014___v189;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2015_recIdents;
            RAST._IExpr _out502;
            DCOMP._IOwnership _out503;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out504;
            (this).GenExpr(_2012_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out502, out _out503, out _out504);
            _2013_recursiveGen = _out502;
            _2014___v189 = _out503;
            _2015_recIdents = _out504;
            readIdents = _2015_recIdents;
            r = ((_2013_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
          DAST._IExpression _2016_on = _source96.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2017_field = _source96.dtor_field;
          bool _2018_isDatatype = _source96.dtor_onDatatype;
          bool _2019_isStatic = _source96.dtor_isStatic;
          BigInteger _2020_arity = _source96.dtor_arity;
          {
            RAST._IExpr _2021_onExpr;
            DCOMP._IOwnership _2022_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2023_recIdents;
            RAST._IExpr _out507;
            DCOMP._IOwnership _out508;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out509;
            (this).GenExpr(_2016_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out507, out _out508, out _out509);
            _2021_onExpr = _out507;
            _2022_onOwned = _out508;
            _2023_recIdents = _out509;
            Dafny.ISequence<Dafny.Rune> _2024_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _2025_onString;
            _2025_onString = (_2021_onExpr)._ToString(DCOMP.__default.IND);
            if (_2019_isStatic) {
              _2024_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2025_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_2017_field));
            } else {
              _2024_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _2024_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2024_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2025_onString), ((object.Equals(_2022_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _2026_args;
              _2026_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _2027_i;
              _2027_i = BigInteger.Zero;
              while ((_2027_i) < (_2020_arity)) {
                if ((_2027_i).Sign == 1) {
                  _2026_args = Dafny.Sequence<Dafny.Rune>.Concat(_2026_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _2026_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2026_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_2027_i));
                _2027_i = (_2027_i) + (BigInteger.One);
              }
              _2024_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2024_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2026_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _2024_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2024_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_2017_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2026_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _2024_s = Dafny.Sequence<Dafny.Rune>.Concat(_2024_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _2024_s = Dafny.Sequence<Dafny.Rune>.Concat(_2024_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _2028_typeShape;
            _2028_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _2029_i;
            _2029_i = BigInteger.Zero;
            while ((_2029_i) < (_2020_arity)) {
              if ((_2029_i).Sign == 1) {
                _2028_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2028_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2028_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2028_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _2029_i = (_2029_i) + (BigInteger.One);
            }
            _2028_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2028_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _2024_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _2024_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _2028_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_2024_s);
            RAST._IExpr _out510;
            DCOMP._IOwnership _out511;
            (this).FromOwned(r, expectedOwnership, out _out510, out _out511);
            r = _out510;
            resultingOwnership = _out511;
            readIdents = _2023_recIdents;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_Select) {
          DAST._IExpression expr0 = _source96.dtor_expr;
          if (expr0.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2030_c = expr0.dtor_Companion_a0;
            Dafny.ISequence<DAST._IType> _2031_typeArgs = expr0.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _2032_field = _source96.dtor_field;
            bool _2033_isConstant = _source96.dtor_isConstant;
            bool _2034_isDatatype = _source96.dtor_onDatatype;
            DAST._IType _2035_fieldType = _source96.dtor_fieldType;
            {
              RAST._IExpr _2036_onExpr;
              DCOMP._IOwnership _2037_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2038_recIdents;
              RAST._IExpr _out512;
              DCOMP._IOwnership _out513;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out514;
              (this).GenExpr(DAST.Expression.create_Companion(_2030_c, _2031_typeArgs), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out512, out _out513, out _out514);
              _2036_onExpr = _out512;
              _2037_onOwned = _out513;
              _2038_recIdents = _out514;
              r = ((_2036_onExpr).MSel(DCOMP.__default.escapeName(_2032_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out515;
              DCOMP._IOwnership _out516;
              (this).FromOwned(r, expectedOwnership, out _out515, out _out516);
              r = _out515;
              resultingOwnership = _out516;
              readIdents = _2038_recIdents;
              return ;
            }
            goto after_match41;
          }
        }
      }
      {
        if (_source96.is_Select) {
          DAST._IExpression _2039_on = _source96.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2040_field = _source96.dtor_field;
          bool _2041_isConstant = _source96.dtor_isConstant;
          bool _2042_isDatatype = _source96.dtor_onDatatype;
          DAST._IType _2043_fieldType = _source96.dtor_fieldType;
          {
            if (_2042_isDatatype) {
              RAST._IExpr _2044_onExpr;
              DCOMP._IOwnership _2045_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2046_recIdents;
              RAST._IExpr _out517;
              DCOMP._IOwnership _out518;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out519;
              (this).GenExpr(_2039_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out517, out _out518, out _out519);
              _2044_onExpr = _out517;
              _2045_onOwned = _out518;
              _2046_recIdents = _out519;
              r = ((_2044_onExpr).Sel(DCOMP.__default.escapeName(_2040_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _2047_typ;
              RAST._IType _out520;
              _out520 = (this).GenType(_2043_fieldType, DCOMP.GenTypeContext.@default());
              _2047_typ = _out520;
              RAST._IExpr _out521;
              DCOMP._IOwnership _out522;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out521, out _out522);
              r = _out521;
              resultingOwnership = _out522;
              readIdents = _2046_recIdents;
            } else {
              RAST._IExpr _2048_onExpr;
              DCOMP._IOwnership _2049_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2050_recIdents;
              RAST._IExpr _out523;
              DCOMP._IOwnership _out524;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
              (this).GenExpr(_2039_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out523, out _out524, out _out525);
              _2048_onExpr = _out523;
              _2049_onOwned = _out524;
              _2050_recIdents = _out525;
              r = _2048_onExpr;
              if (!object.Equals(_2048_onExpr, RAST.__default.self)) {
                RAST._IExpr _source98 = _2048_onExpr;
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
              r = (r).Sel(DCOMP.__default.escapeName(_2040_field));
              if (_2041_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out526;
              DCOMP._IOwnership _out527;
              (this).FromOwned(r, expectedOwnership, out _out526, out _out527);
              r = _out526;
              resultingOwnership = _out527;
              readIdents = _2050_recIdents;
            }
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_Index) {
          DAST._IExpression _2051_on = _source96.dtor_expr;
          DAST._ICollKind _2052_collKind = _source96.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2053_indices = _source96.dtor_indices;
          {
            RAST._IExpr _2054_onExpr;
            DCOMP._IOwnership _2055_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2056_recIdents;
            RAST._IExpr _out528;
            DCOMP._IOwnership _out529;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out530;
            (this).GenExpr(_2051_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out528, out _out529, out _out530);
            _2054_onExpr = _out528;
            _2055_onOwned = _out529;
            _2056_recIdents = _out530;
            readIdents = _2056_recIdents;
            r = _2054_onExpr;
            bool _2057_hadArray;
            _2057_hadArray = false;
            if (object.Equals(_2052_collKind, DAST.CollKind.create_Array())) {
              r = ((this).read__macro).Apply1(r);
              _2057_hadArray = true;
              if ((new BigInteger((_2053_indices).Count)) > (BigInteger.One)) {
                r = (r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
              }
            }
            BigInteger _hi46 = new BigInteger((_2053_indices).Count);
            for (BigInteger _2058_i = BigInteger.Zero; _2058_i < _hi46; _2058_i++) {
              if (object.Equals(_2052_collKind, DAST.CollKind.create_Array())) {
                RAST._IExpr _2059_idx;
                DCOMP._IOwnership _2060_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2061_recIdentsIdx;
                RAST._IExpr _out531;
                DCOMP._IOwnership _out532;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out533;
                (this).GenExpr((_2053_indices).Select(_2058_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out531, out _out532, out _out533);
                _2059_idx = _out531;
                _2060_idxOwned = _out532;
                _2061_recIdentsIdx = _out533;
                _2059_idx = RAST.__default.IntoUsize(_2059_idx);
                r = RAST.Expr.create_SelectIndex(r, _2059_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2061_recIdentsIdx);
              } else {
                RAST._IExpr _2062_idx;
                DCOMP._IOwnership _2063_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2064_recIdentsIdx;
                RAST._IExpr _out534;
                DCOMP._IOwnership _out535;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out536;
                (this).GenExpr((_2053_indices).Select(_2058_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out534, out _out535, out _out536);
                _2062_idx = _out534;
                _2063_idxOwned = _out535;
                _2064_recIdentsIdx = _out536;
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_2062_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2064_recIdentsIdx);
              }
            }
            if (_2057_hadArray) {
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
          DAST._IExpression _2065_on = _source96.dtor_expr;
          bool _2066_isArray = _source96.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _2067_low = _source96.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _2068_high = _source96.dtor_high;
          {
            RAST._IExpr _2069_onExpr;
            DCOMP._IOwnership _2070_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2071_recIdents;
            RAST._IExpr _out539;
            DCOMP._IOwnership _out540;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
            (this).GenExpr(_2065_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out539, out _out540, out _out541);
            _2069_onExpr = _out539;
            _2070_onOwned = _out540;
            _2071_recIdents = _out541;
            readIdents = _2071_recIdents;
            Dafny.ISequence<Dafny.Rune> _2072_methodName;
            if ((_2067_low).is_Some) {
              if ((_2068_high).is_Some) {
                _2072_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice");
              } else {
                _2072_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop");
              }
            } else if ((_2068_high).is_Some) {
              _2072_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take");
            } else {
              _2072_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            }
            Dafny.ISequence<RAST._IExpr> _2073_arguments;
            _2073_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source99 = _2067_low;
            {
              if (_source99.is_Some) {
                DAST._IExpression _2074_l = _source99.dtor_value;
                {
                  RAST._IExpr _2075_lExpr;
                  DCOMP._IOwnership _2076___v192;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2077_recIdentsL;
                  RAST._IExpr _out542;
                  DCOMP._IOwnership _out543;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out544;
                  (this).GenExpr(_2074_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out542, out _out543, out _out544);
                  _2075_lExpr = _out542;
                  _2076___v192 = _out543;
                  _2077_recIdentsL = _out544;
                  _2073_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2073_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2075_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2077_recIdentsL);
                }
                goto after_match44;
              }
            }
            {
            }
          after_match44: ;
            Std.Wrappers._IOption<DAST._IExpression> _source100 = _2068_high;
            {
              if (_source100.is_Some) {
                DAST._IExpression _2078_h = _source100.dtor_value;
                {
                  RAST._IExpr _2079_hExpr;
                  DCOMP._IOwnership _2080___v193;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2081_recIdentsH;
                  RAST._IExpr _out545;
                  DCOMP._IOwnership _out546;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out547;
                  (this).GenExpr(_2078_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out545, out _out546, out _out547);
                  _2079_hExpr = _out545;
                  _2080___v193 = _out546;
                  _2081_recIdentsH = _out547;
                  _2073_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2073_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2079_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2081_recIdentsH);
                }
                goto after_match45;
              }
            }
            {
            }
          after_match45: ;
            r = _2069_onExpr;
            if (_2066_isArray) {
              if (!(_2072_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _2072_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2072_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _2072_methodName))).Apply(_2073_arguments);
            } else {
              if (!(_2072_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_2072_methodName)).Apply(_2073_arguments);
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
          DAST._IExpression _2082_on = _source96.dtor_expr;
          BigInteger _2083_idx = _source96.dtor_index;
          DAST._IType _2084_fieldType = _source96.dtor_fieldType;
          {
            RAST._IExpr _2085_onExpr;
            DCOMP._IOwnership _2086_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2087_recIdents;
            RAST._IExpr _out550;
            DCOMP._IOwnership _out551;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out552;
            (this).GenExpr(_2082_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out550, out _out551, out _out552);
            _2085_onExpr = _out550;
            _2086_onOwnership = _out551;
            _2087_recIdents = _out552;
            Dafny.ISequence<Dafny.Rune> _2088_selName;
            _2088_selName = Std.Strings.__default.OfNat(_2083_idx);
            DAST._IType _source101 = _2084_fieldType;
            {
              if (_source101.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2089_tps = _source101.dtor_Tuple_a0;
                if (((_2084_fieldType).is_Tuple) && ((new BigInteger((_2089_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _2088_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2088_selName);
                }
                goto after_match46;
              }
            }
            {
            }
          after_match46: ;
            r = ((_2085_onExpr).Sel(_2088_selName)).Clone();
            RAST._IExpr _out553;
            DCOMP._IOwnership _out554;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out553, out _out554);
            r = _out553;
            resultingOwnership = _out554;
            readIdents = _2087_recIdents;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_Call) {
          DAST._IExpression _2090_on = _source96.dtor_on;
          DAST._ICallName _2091_name = _source96.dtor_callName;
          Dafny.ISequence<DAST._IType> _2092_typeArgs = _source96.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2093_args = _source96.dtor_args;
          {
            Dafny.ISequence<RAST._IExpr> _2094_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2095_recIdents;
            Dafny.ISequence<RAST._IType> _2096_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _2097_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out555;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out556;
            Dafny.ISequence<RAST._IType> _out557;
            Std.Wrappers._IOption<DAST._IResolvedType> _out558;
            (this).GenArgs(selfIdent, _2091_name, _2092_typeArgs, _2093_args, env, out _out555, out _out556, out _out557, out _out558);
            _2094_argExprs = _out555;
            _2095_recIdents = _out556;
            _2096_typeExprs = _out557;
            _2097_fullNameQualifier = _out558;
            readIdents = _2095_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source102 = _2097_fullNameQualifier;
            {
              if (_source102.is_Some) {
                DAST._IResolvedType value11 = _source102.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2098_path = value11.dtor_path;
                Dafny.ISequence<DAST._IType> _2099_onTypeArgs = value11.dtor_typeArgs;
                DAST._IResolvedTypeBase _2100_base = value11.dtor_kind;
                RAST._IExpr _2101_fullPath;
                RAST._IExpr _out559;
                _out559 = DCOMP.COMP.GenPathExpr(_2098_path);
                _2101_fullPath = _out559;
                Dafny.ISequence<RAST._IType> _2102_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out560;
                _out560 = (this).GenTypeArgs(_2099_onTypeArgs, DCOMP.GenTypeContext.@default());
                _2102_onTypeExprs = _out560;
                RAST._IExpr _2103_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _2104_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2105_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_2100_base).is_Trait) || ((_2100_base).is_Class)) {
                  RAST._IExpr _out561;
                  DCOMP._IOwnership _out562;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out563;
                  (this).GenExpr(_2090_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out561, out _out562, out _out563);
                  _2103_onExpr = _out561;
                  _2104_recOwnership = _out562;
                  _2105_recIdents = _out563;
                  _2103_onExpr = ((this).read__macro).Apply1(_2103_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2105_recIdents);
                } else {
                  RAST._IExpr _out564;
                  DCOMP._IOwnership _out565;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out566;
                  (this).GenExpr(_2090_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out564, out _out565, out _out566);
                  _2103_onExpr = _out564;
                  _2104_recOwnership = _out565;
                  _2105_recIdents = _out566;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2105_recIdents);
                }
                r = ((((_2101_fullPath).ApplyType(_2102_onTypeExprs)).MSel(DCOMP.__default.escapeName((_2091_name).dtor_name))).ApplyType(_2096_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_2103_onExpr), _2094_argExprs));
                RAST._IExpr _out567;
                DCOMP._IOwnership _out568;
                (this).FromOwned(r, expectedOwnership, out _out567, out _out568);
                r = _out567;
                resultingOwnership = _out568;
                goto after_match47;
              }
            }
            {
              RAST._IExpr _2106_onExpr;
              DCOMP._IOwnership _2107___v199;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2108_recIdents;
              RAST._IExpr _out569;
              DCOMP._IOwnership _out570;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out571;
              (this).GenExpr(_2090_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out569, out _out570, out _out571);
              _2106_onExpr = _out569;
              _2107___v199 = _out570;
              _2108_recIdents = _out571;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2108_recIdents);
              Dafny.ISequence<Dafny.Rune> _2109_renderedName;
              DAST._ICallName _source103 = _2091_name;
              {
                if (_source103.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _2110_ident = _source103.dtor_name;
                  _2109_renderedName = DCOMP.__default.escapeName(_2110_ident);
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
                  _2109_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                  goto after_match48;
                }
              }
              {
                _2109_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
              }
            after_match48: ;
              DAST._IExpression _source104 = _2090_on;
              {
                if (_source104.is_Companion) {
                  {
                    _2106_onExpr = (_2106_onExpr).MSel(_2109_renderedName);
                  }
                  goto after_match49;
                }
              }
              {
                {
                  if (!object.Equals(_2106_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source105 = _2091_name;
                    {
                      if (_source105.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType2 = _source105.dtor_onType;
                        if (onType2.is_Some) {
                          DAST._IType _2111_tpe = onType2.dtor_value;
                          RAST._IType _2112_typ;
                          RAST._IType _out572;
                          _out572 = (this).GenType(_2111_tpe, DCOMP.GenTypeContext.@default());
                          _2112_typ = _out572;
                          if ((_2112_typ).IsObjectOrPointer()) {
                            _2106_onExpr = ((this).read__macro).Apply1(_2106_onExpr);
                          }
                          goto after_match50;
                        }
                      }
                    }
                    {
                    }
                  after_match50: ;
                  }
                  _2106_onExpr = (_2106_onExpr).Sel(_2109_renderedName);
                }
              }
            after_match49: ;
              r = ((_2106_onExpr).ApplyType(_2096_typeExprs)).Apply(_2094_argExprs);
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
          Dafny.ISequence<DAST._IFormal> _2113_paramsDafny = _source96.dtor_params;
          DAST._IType _2114_retType = _source96.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2115_body = _source96.dtor_body;
          {
            Dafny.ISequence<RAST._IFormal> _2116_params;
            Dafny.ISequence<RAST._IFormal> _out575;
            _out575 = (this).GenParams(_2113_paramsDafny);
            _2116_params = _out575;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2117_paramNames;
            _2117_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2118_paramTypesMap;
            _2118_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi47 = new BigInteger((_2116_params).Count);
            for (BigInteger _2119_i = BigInteger.Zero; _2119_i < _hi47; _2119_i++) {
              Dafny.ISequence<Dafny.Rune> _2120_name;
              _2120_name = ((_2116_params).Select(_2119_i)).dtor_name;
              _2117_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2117_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2120_name));
              _2118_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2118_paramTypesMap, _2120_name, ((_2116_params).Select(_2119_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _2121_subEnv;
            _2121_subEnv = ((env).ToOwned()).merge(DCOMP.Environment.create(_2117_paramNames, _2118_paramTypesMap));
            RAST._IExpr _2122_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2123_recIdents;
            DCOMP._IEnvironment _2124___v210;
            RAST._IExpr _out576;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out577;
            DCOMP._IEnvironment _out578;
            (this).GenStmts(_2115_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _2121_subEnv, true, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out576, out _out577, out _out578);
            _2122_recursiveGen = _out576;
            _2123_recIdents = _out577;
            _2124___v210 = _out578;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _2123_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2123_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_2125_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll7 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_7 in (_2125_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _2126_name = (Dafny.ISequence<Dafny.Rune>)_compr_7;
                if ((_2125_paramNames).Contains(_2126_name)) {
                  _coll7.Add(_2126_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll7);
            }))())(_2117_paramNames));
            RAST._IExpr _2127_allReadCloned;
            _2127_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_2123_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _2128_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_2123_recIdents).Elements) {
                _2128_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_2123_recIdents).Contains(_2128_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 4877)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_2128_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _2129_selfCloned;
                DCOMP._IOwnership _2130___v211;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2131___v212;
                RAST._IExpr _out579;
                DCOMP._IOwnership _out580;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out581;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out579, out _out580, out _out581);
                _2129_selfCloned = _out579;
                _2130___v211 = _out580;
                _2131___v212 = _out581;
                _2127_allReadCloned = (_2127_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2129_selfCloned)));
              } else if (!((_2117_paramNames).Contains(_2128_next))) {
                RAST._IExpr _2132_copy;
                _2132_copy = (RAST.Expr.create_Identifier(_2128_next)).Clone();
                _2127_allReadCloned = (_2127_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2128_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2132_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2128_next));
              }
              _2123_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2123_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2128_next));
            }
            RAST._IType _2133_retTypeGen;
            RAST._IType _out582;
            _out582 = (this).GenType(_2114_retType, DCOMP.GenTypeContext.InFn());
            _2133_retTypeGen = _out582;
            r = RAST.Expr.create_Block((_2127_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_2116_params, Std.Wrappers.Option<RAST._IType>.create_Some(_2133_retTypeGen), RAST.Expr.create_Block(_2122_recursiveGen)))));
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
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2134_values = _source96.dtor_values;
          DAST._IType _2135_retType = _source96.dtor_retType;
          DAST._IExpression _2136_expr = _source96.dtor_expr;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2137_paramNames;
            _2137_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2138_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out585;
            _out585 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2139_value) => {
              return (_2139_value).dtor__0;
            })), _2134_values));
            _2138_paramFormals = _out585;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2140_paramTypes;
            _2140_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2141_paramNamesSet;
            _2141_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi48 = new BigInteger((_2134_values).Count);
            for (BigInteger _2142_i = BigInteger.Zero; _2142_i < _hi48; _2142_i++) {
              Dafny.ISequence<Dafny.Rune> _2143_name;
              _2143_name = (((_2134_values).Select(_2142_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2144_rName;
              _2144_rName = DCOMP.__default.escapeName(_2143_name);
              _2137_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2137_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2144_rName));
              _2140_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2140_paramTypes, _2144_rName, ((_2138_paramFormals).Select(_2142_i)).dtor_tpe);
              _2141_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2141_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2144_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi49 = new BigInteger((_2134_values).Count);
            for (BigInteger _2145_i = BigInteger.Zero; _2145_i < _hi49; _2145_i++) {
              RAST._IType _2146_typeGen;
              RAST._IType _out586;
              _out586 = (this).GenType((((_2134_values).Select(_2145_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.InFn());
              _2146_typeGen = _out586;
              RAST._IExpr _2147_valueGen;
              DCOMP._IOwnership _2148___v213;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2149_recIdents;
              RAST._IExpr _out587;
              DCOMP._IOwnership _out588;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out589;
              (this).GenExpr(((_2134_values).Select(_2145_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out587, out _out588, out _out589);
              _2147_valueGen = _out587;
              _2148___v213 = _out588;
              _2149_recIdents = _out589;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_2134_values).Select(_2145_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2146_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2147_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2149_recIdents);
            }
            DCOMP._IEnvironment _2150_newEnv;
            _2150_newEnv = DCOMP.Environment.create(_2137_paramNames, _2140_paramTypes);
            RAST._IExpr _2151_recGen;
            DCOMP._IOwnership _2152_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2153_recIdents;
            RAST._IExpr _out590;
            DCOMP._IOwnership _out591;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out592;
            (this).GenExpr(_2136_expr, selfIdent, _2150_newEnv, expectedOwnership, out _out590, out _out591, out _out592);
            _2151_recGen = _out590;
            _2152_recOwned = _out591;
            _2153_recIdents = _out592;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2153_recIdents, _2141_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2151_recGen));
            RAST._IExpr _out593;
            DCOMP._IOwnership _out594;
            (this).FromOwnership(r, _2152_recOwned, expectedOwnership, out _out593, out _out594);
            r = _out593;
            resultingOwnership = _out594;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2154_name = _source96.dtor_ident;
          DAST._IType _2155_tpe = _source96.dtor_typ;
          DAST._IExpression _2156_value = _source96.dtor_value;
          DAST._IExpression _2157_iifeBody = _source96.dtor_iifeBody;
          {
            RAST._IExpr _2158_valueGen;
            DCOMP._IOwnership _2159___v214;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2160_recIdents;
            RAST._IExpr _out595;
            DCOMP._IOwnership _out596;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out597;
            (this).GenExpr(_2156_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out595, out _out596, out _out597);
            _2158_valueGen = _out595;
            _2159___v214 = _out596;
            _2160_recIdents = _out597;
            readIdents = _2160_recIdents;
            RAST._IType _2161_valueTypeGen;
            RAST._IType _out598;
            _out598 = (this).GenType(_2155_tpe, DCOMP.GenTypeContext.InFn());
            _2161_valueTypeGen = _out598;
            RAST._IExpr _2162_bodyGen;
            DCOMP._IOwnership _2163___v215;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2164_bodyIdents;
            RAST._IExpr _out599;
            DCOMP._IOwnership _out600;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out601;
            (this).GenExpr(_2157_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out599, out _out600, out _out601);
            _2162_bodyGen = _out599;
            _2163___v215 = _out600;
            _2164_bodyIdents = _out601;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2164_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_2154_name)))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_2154_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_2161_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2158_valueGen))).Then(_2162_bodyGen));
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
          DAST._IExpression _2165_func = _source96.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2166_args = _source96.dtor_args;
          {
            RAST._IExpr _2167_funcExpr;
            DCOMP._IOwnership _2168___v216;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2169_recIdents;
            RAST._IExpr _out604;
            DCOMP._IOwnership _out605;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out606;
            (this).GenExpr(_2165_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out604, out _out605, out _out606);
            _2167_funcExpr = _out604;
            _2168___v216 = _out605;
            _2169_recIdents = _out606;
            readIdents = _2169_recIdents;
            Dafny.ISequence<RAST._IExpr> _2170_rArgs;
            _2170_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi50 = new BigInteger((_2166_args).Count);
            for (BigInteger _2171_i = BigInteger.Zero; _2171_i < _hi50; _2171_i++) {
              RAST._IExpr _2172_argExpr;
              DCOMP._IOwnership _2173_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2174_argIdents;
              RAST._IExpr _out607;
              DCOMP._IOwnership _out608;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out609;
              (this).GenExpr((_2166_args).Select(_2171_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out607, out _out608, out _out609);
              _2172_argExpr = _out607;
              _2173_argOwned = _out608;
              _2174_argIdents = _out609;
              _2170_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2170_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2172_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2174_argIdents);
            }
            r = (_2167_funcExpr).Apply(_2170_rArgs);
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
          DAST._IExpression _2175_on = _source96.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2176_dType = _source96.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2177_variant = _source96.dtor_variant;
          {
            RAST._IExpr _2178_exprGen;
            DCOMP._IOwnership _2179___v217;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2180_recIdents;
            RAST._IExpr _out612;
            DCOMP._IOwnership _out613;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out614;
            (this).GenExpr(_2175_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out612, out _out613, out _out614);
            _2178_exprGen = _out612;
            _2179___v217 = _out613;
            _2180_recIdents = _out614;
            RAST._IType _2181_dTypePath;
            RAST._IType _out615;
            _out615 = DCOMP.COMP.GenPath(_2176_dType);
            _2181_dTypePath = _out615;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2178_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_2181_dTypePath).MSel(DCOMP.__default.escapeName(_2177_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out616;
            DCOMP._IOwnership _out617;
            (this).FromOwned(r, expectedOwnership, out _out616, out _out617);
            r = _out616;
            resultingOwnership = _out617;
            readIdents = _2180_recIdents;
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
          DAST._IExpression _2182_of = _source96.dtor_of;
          {
            RAST._IExpr _2183_exprGen;
            DCOMP._IOwnership _2184___v218;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2185_recIdents;
            RAST._IExpr _out620;
            DCOMP._IOwnership _out621;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
            (this).GenExpr(_2182_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out620, out _out621, out _out622);
            _2183_exprGen = _out620;
            _2184___v218 = _out621;
            _2185_recIdents = _out622;
            r = ((_2183_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out623;
            DCOMP._IOwnership _out624;
            (this).FromOwned(r, expectedOwnership, out _out623, out _out624);
            r = _out623;
            resultingOwnership = _out624;
            readIdents = _2185_recIdents;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_SeqBoundedPool) {
          DAST._IExpression _2186_of = _source96.dtor_of;
          bool _2187_includeDuplicates = _source96.dtor_includeDuplicates;
          {
            RAST._IExpr _2188_exprGen;
            DCOMP._IOwnership _2189___v219;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2190_recIdents;
            RAST._IExpr _out625;
            DCOMP._IOwnership _out626;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out627;
            (this).GenExpr(_2186_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out625, out _out626, out _out627);
            _2188_exprGen = _out625;
            _2189___v219 = _out626;
            _2190_recIdents = _out627;
            r = ((_2188_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2187_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out628;
            DCOMP._IOwnership _out629;
            (this).FromOwned(r, expectedOwnership, out _out628, out _out629);
            r = _out628;
            resultingOwnership = _out629;
            readIdents = _2190_recIdents;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_MapBoundedPool) {
          DAST._IExpression _2191_of = _source96.dtor_of;
          {
            RAST._IExpr _2192_exprGen;
            DCOMP._IOwnership _2193___v220;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2194_recIdents;
            RAST._IExpr _out630;
            DCOMP._IOwnership _out631;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out632;
            (this).GenExpr(_2191_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out630, out _out631, out _out632);
            _2192_exprGen = _out630;
            _2193___v220 = _out631;
            _2194_recIdents = _out632;
            r = ((((_2192_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2194_recIdents;
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
          DAST._IExpression _2195_lo = _source96.dtor_lo;
          DAST._IExpression _2196_hi = _source96.dtor_hi;
          bool _2197_up = _source96.dtor_up;
          {
            RAST._IExpr _2198_lo;
            DCOMP._IOwnership _2199___v221;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2200_recIdentsLo;
            RAST._IExpr _out635;
            DCOMP._IOwnership _out636;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out637;
            (this).GenExpr(_2195_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out635, out _out636, out _out637);
            _2198_lo = _out635;
            _2199___v221 = _out636;
            _2200_recIdentsLo = _out637;
            RAST._IExpr _2201_hi;
            DCOMP._IOwnership _2202___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2203_recIdentsHi;
            RAST._IExpr _out638;
            DCOMP._IOwnership _out639;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out640;
            (this).GenExpr(_2196_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out638, out _out639, out _out640);
            _2201_hi = _out638;
            _2202___v222 = _out639;
            _2203_recIdentsHi = _out640;
            if (_2197_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2198_lo, _2201_hi));
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2201_hi, _2198_lo));
            }
            RAST._IExpr _out641;
            DCOMP._IOwnership _out642;
            (this).FromOwned(r, expectedOwnership, out _out641, out _out642);
            r = _out641;
            resultingOwnership = _out642;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2200_recIdentsLo, _2203_recIdentsHi);
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_UnboundedIntRange) {
          DAST._IExpression _2204_start = _source96.dtor_start;
          bool _2205_up = _source96.dtor_up;
          {
            RAST._IExpr _2206_start;
            DCOMP._IOwnership _2207___v223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2208_recIdentStart;
            RAST._IExpr _out643;
            DCOMP._IOwnership _out644;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out645;
            (this).GenExpr(_2204_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out643, out _out644, out _out645);
            _2206_start = _out643;
            _2207___v223 = _out644;
            _2208_recIdentStart = _out645;
            if (_2205_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).Apply1(_2206_start);
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).Apply1(_2206_start);
            }
            RAST._IExpr _out646;
            DCOMP._IOwnership _out647;
            (this).FromOwned(r, expectedOwnership, out _out646, out _out647);
            r = _out646;
            resultingOwnership = _out647;
            readIdents = _2208_recIdentStart;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source96.is_MapBuilder) {
          DAST._IType _2209_keyType = _source96.dtor_keyType;
          DAST._IType _2210_valueType = _source96.dtor_valueType;
          {
            RAST._IType _2211_kType;
            RAST._IType _out648;
            _out648 = (this).GenType(_2209_keyType, DCOMP.GenTypeContext.@default());
            _2211_kType = _out648;
            RAST._IType _2212_vType;
            RAST._IType _out649;
            _out649 = (this).GenType(_2210_valueType, DCOMP.GenTypeContext.@default());
            _2212_vType = _out649;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2211_kType, _2212_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
          DAST._IType _2213_elemType = _source96.dtor_elemType;
          {
            RAST._IType _2214_eType;
            RAST._IType _out652;
            _out652 = (this).GenType(_2213_elemType, DCOMP.GenTypeContext.@default());
            _2214_eType = _out652;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2214_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
        DAST._IType _2215_elemType = _source96.dtor_elemType;
        DAST._IExpression _2216_collection = _source96.dtor_collection;
        bool _2217_is__forall = _source96.dtor_is__forall;
        DAST._IExpression _2218_lambda = _source96.dtor_lambda;
        {
          RAST._IType _2219_tpe;
          RAST._IType _out655;
          _out655 = (this).GenType(_2215_elemType, DCOMP.GenTypeContext.@default());
          _2219_tpe = _out655;
          RAST._IExpr _2220_collectionGen;
          DCOMP._IOwnership _2221___v224;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2222_recIdents;
          RAST._IExpr _out656;
          DCOMP._IOwnership _out657;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out658;
          (this).GenExpr(_2216_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out656, out _out657, out _out658);
          _2220_collectionGen = _out656;
          _2221___v224 = _out657;
          _2222_recIdents = _out658;
          Dafny.ISequence<DAST._IAttribute> _2223_extraAttributes;
          _2223_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2216_collection).is_IntRange) || ((_2216_collection).is_UnboundedIntRange)) || ((_2216_collection).is_SeqBoundedPool)) {
            _2223_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2218_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2224_formals;
            _2224_formals = (_2218_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2225_newFormals;
            _2225_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi51 = new BigInteger((_2224_formals).Count);
            for (BigInteger _2226_i = BigInteger.Zero; _2226_i < _hi51; _2226_i++) {
              var _pat_let_tv4 = _2223_extraAttributes;
              var _pat_let_tv5 = _2224_formals;
              _2225_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2225_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2224_formals).Select(_2226_i), _pat_let34_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let34_0, _2227_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv4, ((_pat_let_tv5).Select(_2226_i)).dtor_attributes), _pat_let35_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let35_0, _2228_dt__update_hattributes_h0 => DAST.Formal.create((_2227_dt__update__tmp_h0).dtor_name, (_2227_dt__update__tmp_h0).dtor_typ, _2228_dt__update_hattributes_h0)))))));
            }
            DAST._IExpression _2229_newLambda;
            DAST._IExpression _2230_dt__update__tmp_h1 = _2218_lambda;
            Dafny.ISequence<DAST._IFormal> _2231_dt__update_hparams_h0 = _2225_newFormals;
            _2229_newLambda = DAST.Expression.create_Lambda(_2231_dt__update_hparams_h0, (_2230_dt__update__tmp_h1).dtor_retType, (_2230_dt__update__tmp_h1).dtor_body);
            RAST._IExpr _2232_lambdaGen;
            DCOMP._IOwnership _2233___v225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2234_recLambdaIdents;
            RAST._IExpr _out659;
            DCOMP._IOwnership _out660;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out661;
            (this).GenExpr(_2229_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out659, out _out660, out _out661);
            _2232_lambdaGen = _out659;
            _2233___v225 = _out660;
            _2234_recLambdaIdents = _out661;
            Dafny.ISequence<Dafny.Rune> _2235_fn;
            if (_2217_is__forall) {
              _2235_fn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all");
            } else {
              _2235_fn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any");
            }
            r = ((_2220_collectionGen).Sel(_2235_fn)).Apply1(((_2232_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2222_recIdents, _2234_recLambdaIdents);
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
      BigInteger _2236_i;
      _2236_i = BigInteger.Zero;
      while ((_2236_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _2237_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _2238_m;
        RAST._IMod _out664;
        _out664 = (this).GenModule((p).Select(_2236_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2238_m = _out664;
        _2237_generated = (_2238_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_2236_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2237_generated);
        _2236_i = (_2236_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2239_i;
      _2239_i = BigInteger.Zero;
      while ((_2239_i) < (new BigInteger((fullName).Count))) {
        if ((_2239_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2239_i)));
        _2239_i = (_2239_i) + (BigInteger.One);
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