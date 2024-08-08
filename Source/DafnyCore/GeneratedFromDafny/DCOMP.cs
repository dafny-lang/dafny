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
      Dafny.ISequence<Dafny.Rune> _1117___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1117___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1117___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1117___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in123 = (i).Drop(new BigInteger(2));
        i = _in123;
        goto TAIL_CALL_START;
      } else {
        _1117___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1117___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in124 = (i).Drop(BigInteger.One);
        i = _in124;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1118___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1118___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1118___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1118___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in125 = (i).Drop(BigInteger.One);
        i = _in125;
        goto TAIL_CALL_START;
      } else {
        _1118___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1118___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _1119_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1119_r);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeField(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1120_r = (f);
      if ((DCOMP.__default.reserved__fields).Contains(_1120_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1120_r);
      } else {
        return DCOMP.__default.escapeName(f);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeDtor(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1121_r = (f);
      if ((DCOMP.__default.reserved__fields).Contains(_1121_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1121_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": r#_")), _1121_r);
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
        Std.Wrappers._IOption<DAST._IResolvedType> _1122_res = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
          DAST._IType _source51 = (rs).Select(BigInteger.Zero);
          {
            if (_source51.is_UserDefined) {
              DAST._IResolvedType _1123_resolvedType = _source51.dtor_resolved;
              return DCOMP.__default.TraitTypeContainingMethod(_1123_resolvedType, dafnyName);
            }
          }
          {
            return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
          }
        }))();
        Std.Wrappers._IOption<DAST._IResolvedType> _source52 = _1122_res;
        {
          if (_source52.is_Some) {
            return _1122_res;
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
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1124_path = _let_tmp_rhs53.dtor_path;
      Dafny.ISequence<DAST._IType> _1125_typeArgs = _let_tmp_rhs53.dtor_typeArgs;
      DAST._IResolvedTypeBase _1126_kind = _let_tmp_rhs53.dtor_kind;
      Dafny.ISequence<DAST._IAttribute> _1127_attributes = _let_tmp_rhs53.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1128_properMethods = _let_tmp_rhs53.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1129_extendedTypes = _let_tmp_rhs53.dtor_extendedTypes;
      if ((_1128_properMethods).Contains(dafnyName)) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(r);
      } else {
        return DCOMP.__default.TraitTypeContainingMethodAux(_1129_extendedTypes, dafnyName);
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
      DCOMP._IEnvironment _1130_dt__update__tmp_h0 = this;
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1131_dt__update_htypes_h0 = ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType>>)(() => {
        var _coll6 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in ((this).dtor_types).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _1132_k = (Dafny.ISequence<Dafny.Rune>)_compr_6;
          if (((this).dtor_types).Contains(_1132_k)) {
            _coll6.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>(_1132_k, (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,_1132_k)).ToOwned()));
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IType>.FromCollection(_coll6);
      }))();
      return DCOMP.Environment.create((_1130_dt__update__tmp_h0).dtor_names, _1131_dt__update_htypes_h0);
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
      BigInteger _1133_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1133_indexInEnv), ((this).dtor_names).Drop((_1133_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
    public bool HasTestAttribute(Dafny.ISequence<DAST._IAttribute> attributes) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_1134_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_1134_attributes).UniqueElements, false, (((_exists_var_1) => {
        DAST._IAttribute _1135_attribute = (DAST._IAttribute)_exists_var_1;
        return ((_1134_attributes).Contains(_1135_attribute)) && ((((_1135_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"))) && ((new BigInteger(((_1135_attribute).dtor_args).Count)).Sign == 0));
      }))))(attributes);
    }
    public RAST._IMod GenModule(DAST._IModule mod, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      RAST._IMod s = RAST.Mod.Default();
      Dafny.ISequence<Dafny.Rune> _1136_modName;
      _1136_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_1136_modName);
      } else {
        Dafny.ISequence<RAST._IModDecl> _1137_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _1137_body = _out15;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1138_attributes;
        _1138_attributes = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
        if ((this).HasTestAttribute((mod).dtor_attributes)) {
          _1138_attributes = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[cfg(test)]"));
        }
        s = RAST.Mod.create_Mod(_1136_modName, _1138_attributes, _1137_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi5 = new BigInteger((body).Count);
      for (BigInteger _1139_i = BigInteger.Zero; _1139_i < _hi5; _1139_i++) {
        Dafny.ISequence<RAST._IModDecl> _1140_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source53 = (body).Select(_1139_i);
        {
          if (_source53.is_Module) {
            DAST._IModule _1141_m = _source53.dtor_Module_a0;
            RAST._IMod _1142_mm;
            RAST._IMod _out16;
            _out16 = (this).GenModule(_1141_m, containingPath);
            _1142_mm = _out16;
            _1140_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1142_mm));
            goto after_match1;
          }
        }
        {
          if (_source53.is_Class) {
            DAST._IClass _1143_c = _source53.dtor_Class_a0;
            Dafny.ISequence<RAST._IModDecl> _out17;
            _out17 = (this).GenClass(_1143_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1143_c).dtor_name)));
            _1140_generated = _out17;
            goto after_match1;
          }
        }
        {
          if (_source53.is_Trait) {
            DAST._ITrait _1144_t = _source53.dtor_Trait_a0;
            Dafny.ISequence<RAST._IModDecl> _out18;
            _out18 = (this).GenTrait(_1144_t, containingPath);
            _1140_generated = _out18;
            goto after_match1;
          }
        }
        {
          if (_source53.is_Newtype) {
            DAST._INewtype _1145_n = _source53.dtor_Newtype_a0;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenNewtype(_1145_n);
            _1140_generated = _out19;
            goto after_match1;
          }
        }
        {
          if (_source53.is_SynonymType) {
            DAST._ISynonymType _1146_s = _source53.dtor_SynonymType_a0;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenSynonymType(_1146_s);
            _1140_generated = _out20;
            goto after_match1;
          }
        }
        {
          DAST._IDatatype _1147_d = _source53.dtor_Datatype_a0;
          Dafny.ISequence<RAST._IModDecl> _out21;
          _out21 = (this).GenDatatype(_1147_d);
          _1140_generated = _out21;
        }
      after_match1: ;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1140_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1148_genTpConstraint;
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) {
        _1148_genTpConstraint = Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq);
      } else {
        _1148_genTpConstraint = Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType);
      }
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1148_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1148_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1148_genTpConstraint);
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
        for (BigInteger _1149_tpI = BigInteger.Zero; _1149_tpI < _hi6; _1149_tpI++) {
          DAST._ITypeArgDecl _1150_tp;
          _1150_tp = (@params).Select(_1149_tpI);
          DAST._IType _1151_typeArg;
          RAST._ITypeParamDecl _1152_typeParam;
          DAST._IType _out22;
          RAST._ITypeParamDecl _out23;
          (this).GenTypeParam(_1150_tp, out _out22, out _out23);
          _1151_typeArg = _out22;
          _1152_typeParam = _out23;
          RAST._IType _1153_rType;
          RAST._IType _out24;
          _out24 = (this).GenType(_1151_typeArg, DCOMP.GenTypeContext.@default());
          _1153_rType = _out24;
          typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1151_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1153_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1152_typeParam));
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
      Dafny.ISequence<DAST._IType> _1154_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1155_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1156_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1157_whereConstraints;
      Dafny.ISequence<DAST._IType> _out25;
      Dafny.ISequence<RAST._IType> _out26;
      Dafny.ISequence<RAST._ITypeParamDecl> _out27;
      Dafny.ISequence<Dafny.Rune> _out28;
      (this).GenTypeParameters((c).dtor_typeParams, out _out25, out _out26, out _out27, out _out28);
      _1154_typeParamsSeq = _out25;
      _1155_rTypeParams = _out26;
      _1156_rTypeParamsDecls = _out27;
      _1157_whereConstraints = _out28;
      Dafny.ISequence<Dafny.Rune> _1158_constrainedTypeParams;
      _1158_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1156_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1159_fields;
      _1159_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1160_fieldInits;
      _1160_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1161_fieldI = BigInteger.Zero; _1161_fieldI < _hi7; _1161_fieldI++) {
        DAST._IField _1162_field;
        _1162_field = ((c).dtor_fields).Select(_1161_fieldI);
        RAST._IType _1163_fieldType;
        RAST._IType _out29;
        _out29 = (this).GenType(((_1162_field).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
        _1163_fieldType = _out29;
        Dafny.ISequence<Dafny.Rune> _1164_fieldRustName;
        _1164_fieldRustName = DCOMP.__default.escapeName(((_1162_field).dtor_formal).dtor_name);
        _1159_fields = Dafny.Sequence<RAST._IField>.Concat(_1159_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1164_fieldRustName, _1163_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source54 = (_1162_field).dtor_defaultValue;
        {
          if (_source54.is_Some) {
            DAST._IExpression _1165_e = _source54.dtor_value;
            {
              RAST._IExpr _1166_expr;
              DCOMP._IOwnership _1167___v48;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1168___v49;
              RAST._IExpr _out30;
              DCOMP._IOwnership _out31;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
              (this).GenExpr(_1165_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
              _1166_expr = _out30;
              _1167___v48 = _out31;
              _1168___v49 = _out32;
              _1160_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1160_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1164_fieldRustName, _1166_expr)));
            }
            goto after_match2;
          }
        }
        {
          {
            RAST._IExpr _1169_default;
            _1169_default = RAST.__default.std__Default__default;
            if ((_1163_fieldType).IsObjectOrPointer()) {
              _1169_default = (_1163_fieldType).ToNullExpr();
            }
            _1160_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1160_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1164_fieldRustName, _1169_default)));
          }
        }
      after_match2: ;
      }
      BigInteger _hi8 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1170_typeParamI = BigInteger.Zero; _1170_typeParamI < _hi8; _1170_typeParamI++) {
        DAST._IType _1171_typeArg;
        RAST._ITypeParamDecl _1172_typeParam;
        DAST._IType _out33;
        RAST._ITypeParamDecl _out34;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1170_typeParamI), out _out33, out _out34);
        _1171_typeArg = _out33;
        _1172_typeParam = _out34;
        RAST._IType _1173_rTypeArg;
        RAST._IType _out35;
        _out35 = (this).GenType(_1171_typeArg, DCOMP.GenTypeContext.@default());
        _1173_rTypeArg = _out35;
        _1159_fields = Dafny.Sequence<RAST._IField>.Concat(_1159_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1170_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1173_rTypeArg))))));
        _1160_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1160_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1170_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      Dafny.ISequence<Dafny.Rune> _1174_datatypeName;
      _1174_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IStruct _1175_struct;
      _1175_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1174_datatypeName, _1156_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1159_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1175_struct));
      Dafny.ISequence<RAST._IImplMember> _1176_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1177_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out36;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out37;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(path, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Class(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1154_typeParamsSeq, out _out36, out _out37);
      _1176_implBodyRaw = _out36;
      _1177_traitBodies = _out37;
      Dafny.ISequence<RAST._IImplMember> _1178_implBody;
      _1178_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.Type.create_SelfOwned())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel((this).allocate)).ApplyType1(RAST.Type.create_SelfOwned())).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))))), _1176_implBodyRaw);
      RAST._IImpl _1179_i;
      _1179_i = RAST.Impl.create_Impl(_1156_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1174_datatypeName), _1155_rTypeParams), _1157_whereConstraints, _1178_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1179_i)));
      Dafny.ISequence<RAST._IModDecl> _1180_testMethods;
      _1180_testMethods = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((_1174_datatypeName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) {
        BigInteger _hi9 = new BigInteger(((c).dtor_body).Count);
        for (BigInteger _1181_i = BigInteger.Zero; _1181_i < _hi9; _1181_i++) {
          DAST._IMethod _1182_m;
          DAST._IMethod _source55 = ((c).dtor_body).Select(_1181_i);
          {
            DAST._IMethod _1183_m = _source55;
            _1182_m = _1183_m;
          }
        after_match3: ;
          if (((this).HasTestAttribute((_1182_m).dtor_attributes)) && ((new BigInteger(((_1182_m).dtor_params).Count)).Sign == 0)) {
            Dafny.ISequence<Dafny.Rune> _1184_fnName;
            _1184_fnName = DCOMP.__default.escapeName((_1182_m).dtor_name);
            _1180_testMethods = Dafny.Sequence<RAST._IModDecl>.Concat(_1180_testMethods, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[test]")), RAST.Visibility.create_PUB(), RAST.Fn.create(_1184_fnName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))).MSel(_1184_fnName)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())))))));
          }
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1180_testMethods);
      }
      RAST._IType _1185_genSelfPath;
      RAST._IType _out38;
      _out38 = DCOMP.COMP.GenPath(path);
      _1185_genSelfPath = _out38;
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1156_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"))))), RAST.Type.create_TypeApp(_1185_genSelfPath, _1155_rTypeParams), _1157_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any")))))))))));
      BigInteger _hi10 = new BigInteger(((c).dtor_superClasses).Count);
      for (BigInteger _1186_i = BigInteger.Zero; _1186_i < _hi10; _1186_i++) {
        DAST._IType _1187_superClass;
        _1187_superClass = ((c).dtor_superClasses).Select(_1186_i);
        DAST._IType _source56 = _1187_superClass;
        {
          if (_source56.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source56.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1188_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _1189_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
              {
                RAST._IType _1190_pathStr;
                RAST._IType _out39;
                _out39 = DCOMP.COMP.GenPath(_1188_traitPath);
                _1190_pathStr = _out39;
                Dafny.ISequence<RAST._IType> _1191_typeArgs;
                Dafny.ISequence<RAST._IType> _out40;
                _out40 = (this).GenTypeArgs(_1189_typeArgs, DCOMP.GenTypeContext.@default());
                _1191_typeArgs = _out40;
                Dafny.ISequence<RAST._IImplMember> _1192_body;
                _1192_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_1177_traitBodies).Contains(_1188_traitPath)) {
                  _1192_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1177_traitBodies,_1188_traitPath);
                }
                RAST._IType _1193_traitType;
                _1193_traitType = RAST.Type.create_TypeApp(_1190_pathStr, _1191_typeArgs);
                RAST._IModDecl _1194_x;
                _1194_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1156_rTypeParamsDecls, _1193_traitType, RAST.Type.create_TypeApp(_1185_genSelfPath, _1155_rTypeParams), _1157_whereConstraints, _1192_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1194_x));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1156_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_1193_traitType))), RAST.Type.create_TypeApp(_1185_genSelfPath, _1155_rTypeParams), _1157_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(_1193_traitType)))))))));
              }
              goto after_match4;
            }
          }
        }
        {
        }
      after_match4: ;
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1195_typeParamsSeq;
      _1195_typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1196_typeParamDecls;
      _1196_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1197_typeParams;
      _1197_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _hi11 = new BigInteger(((t).dtor_typeParams).Count);
        for (BigInteger _1198_tpI = BigInteger.Zero; _1198_tpI < _hi11; _1198_tpI++) {
          DAST._ITypeArgDecl _1199_tp;
          _1199_tp = ((t).dtor_typeParams).Select(_1198_tpI);
          DAST._IType _1200_typeArg;
          RAST._ITypeParamDecl _1201_typeParamDecl;
          DAST._IType _out41;
          RAST._ITypeParamDecl _out42;
          (this).GenTypeParam(_1199_tp, out _out41, out _out42);
          _1200_typeArg = _out41;
          _1201_typeParamDecl = _out42;
          _1195_typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(_1195_typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1200_typeArg));
          _1196_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1196_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1201_typeParamDecl));
          RAST._IType _1202_typeParam;
          RAST._IType _out43;
          _out43 = (this).GenType(_1200_typeArg, DCOMP.GenTypeContext.@default());
          _1202_typeParam = _out43;
          _1197_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1197_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1202_typeParam));
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1203_fullPath;
      _1203_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1204_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1205___v54;
      Dafny.ISequence<RAST._IImplMember> _out44;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out45;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1203_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Trait(), (t).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1195_typeParamsSeq, out _out44, out _out45);
      _1204_implBody = _out44;
      _1205___v54 = _out45;
      Dafny.ISequence<RAST._IType> _1206_parents;
      _1206_parents = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi12 = new BigInteger(((t).dtor_parents).Count);
      for (BigInteger _1207_i = BigInteger.Zero; _1207_i < _hi12; _1207_i++) {
        RAST._IType _1208_tpe;
        RAST._IType _out46;
        _out46 = (this).GenType(((t).dtor_parents).Select(_1207_i), DCOMP.GenTypeContext.ForTraitParents());
        _1208_tpe = _out46;
        _1206_parents = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.Concat(_1206_parents, Dafny.Sequence<RAST._IType>.FromElements(_1208_tpe)), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply1(RAST.Type.create_DynType(_1208_tpe))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1196_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1197_typeParams), _1206_parents, _1204_implBody)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1209_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1210_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1211_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1212_whereConstraints;
      Dafny.ISequence<DAST._IType> _out47;
      Dafny.ISequence<RAST._IType> _out48;
      Dafny.ISequence<RAST._ITypeParamDecl> _out49;
      Dafny.ISequence<Dafny.Rune> _out50;
      (this).GenTypeParameters((c).dtor_typeParams, out _out47, out _out48, out _out49, out _out50);
      _1209_typeParamsSeq = _out47;
      _1210_rTypeParams = _out48;
      _1211_rTypeParamsDecls = _out49;
      _1212_whereConstraints = _out50;
      Dafny.ISequence<Dafny.Rune> _1213_constrainedTypeParams;
      _1213_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1211_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1214_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source57 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      {
        if (_source57.is_Some) {
          RAST._IType _1215_v = _source57.dtor_value;
          _1214_underlyingType = _1215_v;
          goto after_match5;
        }
      }
      {
        RAST._IType _out51;
        _out51 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
        _1214_underlyingType = _out51;
      }
    after_match5: ;
      DAST._IType _1216_resultingType;
      _1216_resultingType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _1217_newtypeName;
      _1217_newtypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1217_newtypeName, _1211_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1214_underlyingType))))));
      RAST._IExpr _1218_fnBody;
      _1218_fnBody = RAST.Expr.create_Identifier(_1217_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source58 = (c).dtor_witnessExpr;
      {
        if (_source58.is_Some) {
          DAST._IExpression _1219_e = _source58.dtor_value;
          {
            DAST._IExpression _1220_e;
            if (object.Equals((c).dtor_base, _1216_resultingType)) {
              _1220_e = _1219_e;
            } else {
              _1220_e = DAST.Expression.create_Convert(_1219_e, (c).dtor_base, _1216_resultingType);
            }
            RAST._IExpr _1221_eStr;
            DCOMP._IOwnership _1222___v55;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1223___v56;
            RAST._IExpr _out52;
            DCOMP._IOwnership _out53;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out54;
            (this).GenExpr(_1220_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out52, out _out53, out _out54);
            _1221_eStr = _out52;
            _1222___v55 = _out53;
            _1223___v56 = _out54;
            _1218_fnBody = (_1218_fnBody).Apply1(_1221_eStr);
          }
          goto after_match6;
        }
      }
      {
        {
          _1218_fnBody = (_1218_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
    after_match6: ;
      RAST._IImplMember _1224_body;
      _1224_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1218_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source59 = (c).dtor_constraint;
      {
        if (_source59.is_None) {
          goto after_match7;
        }
      }
      {
        DAST._INewtypeConstraint value8 = _source59.dtor_value;
        DAST._IFormal _1225_formal = value8.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _1226_constraintStmts = value8.dtor_constraintStmts;
        RAST._IExpr _1227_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1228___v57;
        DCOMP._IEnvironment _1229_newEnv;
        RAST._IExpr _out55;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out56;
        DCOMP._IEnvironment _out57;
        (this).GenStmts(_1226_constraintStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out55, out _out56, out _out57);
        _1227_rStmts = _out55;
        _1228___v57 = _out56;
        _1229_newEnv = _out57;
        Dafny.ISequence<RAST._IFormal> _1230_rFormals;
        Dafny.ISequence<RAST._IFormal> _out58;
        _out58 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_1225_formal));
        _1230_rFormals = _out58;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1211_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1217_newtypeName), _1210_rTypeParams), _1212_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _1230_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1227_rStmts))))))));
      }
    after_match7: ;
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1211_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1217_newtypeName), _1210_rTypeParams), _1212_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1224_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1211_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1217_newtypeName), _1210_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1211_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1217_newtypeName), _1210_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1214_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1231_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1232_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1233_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1234_whereConstraints;
      Dafny.ISequence<DAST._IType> _out59;
      Dafny.ISequence<RAST._IType> _out60;
      Dafny.ISequence<RAST._ITypeParamDecl> _out61;
      Dafny.ISequence<Dafny.Rune> _out62;
      (this).GenTypeParameters((c).dtor_typeParams, out _out59, out _out60, out _out61, out _out62);
      _1231_typeParamsSeq = _out59;
      _1232_rTypeParams = _out60;
      _1233_rTypeParamsDecls = _out61;
      _1234_whereConstraints = _out62;
      Dafny.ISequence<Dafny.Rune> _1235_constrainedTypeParams;
      _1235_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1233_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<Dafny.Rune> _1236_synonymTypeName;
      _1236_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _1237_resultingType;
      RAST._IType _out63;
      _out63 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
      _1237_resultingType = _out63;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1236_synonymTypeName, _1233_rTypeParamsDecls, _1237_resultingType)));
      Std.Wrappers._IOption<DAST._IExpression> _source60 = (c).dtor_witnessExpr;
      {
        if (_source60.is_Some) {
          DAST._IExpression _1238_e = _source60.dtor_value;
          {
            RAST._IExpr _1239_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1240___v58;
            DCOMP._IEnvironment _1241_newEnv;
            RAST._IExpr _out64;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out65;
            DCOMP._IEnvironment _out66;
            (this).GenStmts((c).dtor_witnessStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out64, out _out65, out _out66);
            _1239_rStmts = _out64;
            _1240___v58 = _out65;
            _1241_newEnv = _out66;
            RAST._IExpr _1242_rExpr;
            DCOMP._IOwnership _1243___v59;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1244___v60;
            RAST._IExpr _out67;
            DCOMP._IOwnership _out68;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out69;
            (this).GenExpr(_1238_e, DCOMP.SelfInfo.create_NoSelf(), _1241_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out67, out _out68, out _out69);
            _1242_rExpr = _out67;
            _1243___v59 = _out68;
            _1244___v60 = _out69;
            Dafny.ISequence<Dafny.Rune> _1245_constantName;
            _1245_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_1245_constantName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1237_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_1239_rStmts).Then(_1242_rExpr)))))));
          }
          goto after_match8;
        }
      }
      {
      }
    after_match8: ;
      return s;
    }
    public bool TypeIsEq(DAST._IType t) {
      DAST._IType _source61 = t;
      {
        if (_source61.is_UserDefined) {
          return true;
        }
      }
      {
        if (_source61.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1246_ts = _source61.dtor_Tuple_a0;
          return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, bool>>((_1247_ts) => Dafny.Helpers.Quantifier<DAST._IType>((_1247_ts).UniqueElements, true, (((_forall_var_5) => {
            DAST._IType _1248_t = (DAST._IType)_forall_var_5;
            return !((_1247_ts).Contains(_1248_t)) || ((this).TypeIsEq(_1248_t));
          }))))(_1246_ts);
        }
      }
      {
        if (_source61.is_Array) {
          DAST._IType _1249_t = _source61.dtor_element;
          return (this).TypeIsEq(_1249_t);
        }
      }
      {
        if (_source61.is_Seq) {
          DAST._IType _1250_t = _source61.dtor_element;
          return (this).TypeIsEq(_1250_t);
        }
      }
      {
        if (_source61.is_Set) {
          DAST._IType _1251_t = _source61.dtor_element;
          return (this).TypeIsEq(_1251_t);
        }
      }
      {
        if (_source61.is_Multiset) {
          DAST._IType _1252_t = _source61.dtor_element;
          return (this).TypeIsEq(_1252_t);
        }
      }
      {
        if (_source61.is_Map) {
          DAST._IType _1253_k = _source61.dtor_key;
          DAST._IType _1254_v = _source61.dtor_value;
          return ((this).TypeIsEq(_1253_k)) && ((this).TypeIsEq(_1254_v));
        }
      }
      {
        if (_source61.is_SetBuilder) {
          DAST._IType _1255_t = _source61.dtor_element;
          return (this).TypeIsEq(_1255_t);
        }
      }
      {
        if (_source61.is_MapBuilder) {
          DAST._IType _1256_k = _source61.dtor_key;
          DAST._IType _1257_v = _source61.dtor_value;
          return ((this).TypeIsEq(_1256_k)) && ((this).TypeIsEq(_1257_v));
        }
      }
      {
        if (_source61.is_Arrow) {
          return false;
        }
      }
      {
        if (_source61.is_Primitive) {
          return true;
        }
      }
      {
        if (_source61.is_Passthrough) {
          return true;
        }
      }
      {
        if (_source61.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _1258_i = _source61.dtor_TypeArg_a0;
          return true;
        }
      }
      {
        return true;
      }
    }
    public bool DatatypeIsEq(DAST._IDatatype c) {
      return (!((c).dtor_isCo)) && (Dafny.Helpers.Id<Func<DAST._IDatatype, bool>>((_1259_c) => Dafny.Helpers.Quantifier<DAST._IDatatypeCtor>(((_1259_c).dtor_ctors).UniqueElements, true, (((_forall_var_6) => {
        DAST._IDatatypeCtor _1260_ctor = (DAST._IDatatypeCtor)_forall_var_6;
        return Dafny.Helpers.Quantifier<DAST._IDatatypeDtor>(((_1260_ctor).dtor_args).UniqueElements, true, (((_forall_var_7) => {
          DAST._IDatatypeDtor _1261_arg = (DAST._IDatatypeDtor)_forall_var_7;
          return !((((_1259_c).dtor_ctors).Contains(_1260_ctor)) && (((_1260_ctor).dtor_args).Contains(_1261_arg))) || ((this).TypeIsEq(((_1261_arg).dtor_formal).dtor_typ));
        })));
      }))))(c));
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1262_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1263_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1264_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1265_whereConstraints;
      Dafny.ISequence<DAST._IType> _out70;
      Dafny.ISequence<RAST._IType> _out71;
      Dafny.ISequence<RAST._ITypeParamDecl> _out72;
      Dafny.ISequence<Dafny.Rune> _out73;
      (this).GenTypeParameters((c).dtor_typeParams, out _out70, out _out71, out _out72, out _out73);
      _1262_typeParamsSeq = _out70;
      _1263_rTypeParams = _out71;
      _1264_rTypeParamsDecls = _out72;
      _1265_whereConstraints = _out73;
      Dafny.ISequence<Dafny.Rune> _1266_datatypeName;
      _1266_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1267_ctors;
      _1267_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      Dafny.ISequence<DAST._IVariance> _1268_variances;
      _1268_variances = Std.Collections.Seq.__default.Map<DAST._ITypeArgDecl, DAST._IVariance>(((System.Func<DAST._ITypeArgDecl, DAST._IVariance>)((_1269_typeParamDecl) => {
        return (_1269_typeParamDecl).dtor_variance;
      })), (c).dtor_typeParams);
      BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1270_i = BigInteger.Zero; _1270_i < _hi13; _1270_i++) {
        DAST._IDatatypeCtor _1271_ctor;
        _1271_ctor = ((c).dtor_ctors).Select(_1270_i);
        Dafny.ISequence<RAST._IField> _1272_ctorArgs;
        _1272_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1273_isNumeric;
        _1273_isNumeric = false;
        BigInteger _hi14 = new BigInteger(((_1271_ctor).dtor_args).Count);
        for (BigInteger _1274_j = BigInteger.Zero; _1274_j < _hi14; _1274_j++) {
          DAST._IDatatypeDtor _1275_dtor;
          _1275_dtor = ((_1271_ctor).dtor_args).Select(_1274_j);
          RAST._IType _1276_formalType;
          RAST._IType _out74;
          _out74 = (this).GenType(((_1275_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
          _1276_formalType = _out74;
          Dafny.ISequence<Dafny.Rune> _1277_formalName;
          _1277_formalName = DCOMP.__default.escapeName(((_1275_dtor).dtor_formal).dtor_name);
          if (((_1274_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1277_formalName))) {
            _1273_isNumeric = true;
          }
          if ((((_1274_j).Sign != 0) && (_1273_isNumeric)) && (!(Std.Strings.__default.OfNat(_1274_j)).Equals(_1277_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1277_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1274_j)));
            _1273_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1272_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1272_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1277_formalName, RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1276_formalType))))));
          } else {
            _1272_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1272_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1277_formalName, _1276_formalType))));
          }
        }
        RAST._IFields _1278_namedFields;
        _1278_namedFields = RAST.Fields.create_NamedFields(_1272_ctorArgs);
        if (_1273_isNumeric) {
          _1278_namedFields = (_1278_namedFields).ToNamelessFields();
        }
        _1267_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1267_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1271_ctor).dtor_name), _1278_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1279_selfPath;
      _1279_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1280_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1281_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out75;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out76;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1279_selfPath, _1262_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype(_1268_variances), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1262_typeParamsSeq, out _out75, out _out76);
      _1280_implBodyRaw = _out75;
      _1281_traitBodies = _out76;
      Dafny.ISequence<RAST._IImplMember> _1282_implBody;
      _1282_implBody = _1280_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1283_emittedFields;
      _1283_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi15 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1284_i = BigInteger.Zero; _1284_i < _hi15; _1284_i++) {
        DAST._IDatatypeCtor _1285_ctor;
        _1285_ctor = ((c).dtor_ctors).Select(_1284_i);
        BigInteger _hi16 = new BigInteger(((_1285_ctor).dtor_args).Count);
        for (BigInteger _1286_j = BigInteger.Zero; _1286_j < _hi16; _1286_j++) {
          DAST._IDatatypeDtor _1287_dtor;
          _1287_dtor = ((_1285_ctor).dtor_args).Select(_1286_j);
          Dafny.ISequence<Dafny.Rune> _1288_callName;
          _1288_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1287_dtor).dtor_callName, DCOMP.__default.escapeName(((_1287_dtor).dtor_formal).dtor_name));
          if (!((_1283_emittedFields).Contains(_1288_callName))) {
            _1283_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1283_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1288_callName));
            RAST._IType _1289_formalType;
            RAST._IType _out77;
            _out77 = (this).GenType(((_1287_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
            _1289_formalType = _out77;
            Dafny.ISequence<RAST._IMatchCase> _1290_cases;
            _1290_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi17 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1291_k = BigInteger.Zero; _1291_k < _hi17; _1291_k++) {
              DAST._IDatatypeCtor _1292_ctor2;
              _1292_ctor2 = ((c).dtor_ctors).Select(_1291_k);
              Dafny.ISequence<Dafny.Rune> _1293_pattern;
              _1293_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1266_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1292_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1294_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1295_hasMatchingField;
              _1295_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1296_patternInner;
              _1296_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1297_isNumeric;
              _1297_isNumeric = false;
              BigInteger _hi18 = new BigInteger(((_1292_ctor2).dtor_args).Count);
              for (BigInteger _1298_l = BigInteger.Zero; _1298_l < _hi18; _1298_l++) {
                DAST._IDatatypeDtor _1299_dtor2;
                _1299_dtor2 = ((_1292_ctor2).dtor_args).Select(_1298_l);
                Dafny.ISequence<Dafny.Rune> _1300_patternName;
                _1300_patternName = DCOMP.__default.escapeDtor(((_1299_dtor2).dtor_formal).dtor_name);
                Dafny.ISequence<Dafny.Rune> _1301_varName;
                _1301_varName = DCOMP.__default.escapeField(((_1299_dtor2).dtor_formal).dtor_name);
                if (((_1298_l).Sign == 0) && ((_1300_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1297_isNumeric = true;
                }
                if (_1297_isNumeric) {
                  _1300_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1299_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1298_l)));
                  _1301_varName = _1300_patternName;
                }
                if (object.Equals(((_1287_dtor).dtor_formal).dtor_name, ((_1299_dtor2).dtor_formal).dtor_name)) {
                  _1295_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1301_varName);
                }
                _1296_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1296_patternInner, _1300_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1297_isNumeric) {
                _1293_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1293_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1296_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1293_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1293_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1296_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1295_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1294_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1295_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1294_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1295_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1294_rhs = (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("field does not exist on this variant"));
              }
              RAST._IMatchCase _1302_ctorMatch;
              _1302_ctorMatch = RAST.MatchCase.create(_1293_pattern, RAST.Expr.create_RawExpr(_1294_rhs));
              _1290_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1290_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1302_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1290_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1290_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1266_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr((this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))))));
            }
            RAST._IExpr _1303_methodBody;
            _1303_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1290_cases);
            _1282_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1282_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1288_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1289_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1303_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _1304_coerceTypes;
      _1304_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1305_rCoerceTypeParams;
      _1305_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _1306_coerceArguments;
      _1306_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _1307_coerceMap;
      _1307_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _1308_rCoerceMap;
      _1308_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1309_coerceMapToArg;
      _1309_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1310_types;
        _1310_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi19 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1311_typeI = BigInteger.Zero; _1311_typeI < _hi19; _1311_typeI++) {
          DAST._ITypeArgDecl _1312_typeParam;
          _1312_typeParam = ((c).dtor_typeParams).Select(_1311_typeI);
          DAST._IType _1313_typeArg;
          RAST._ITypeParamDecl _1314_rTypeParamDecl;
          DAST._IType _out78;
          RAST._ITypeParamDecl _out79;
          (this).GenTypeParam(_1312_typeParam, out _out78, out _out79);
          _1313_typeArg = _out78;
          _1314_rTypeParamDecl = _out79;
          RAST._IType _1315_rTypeArg;
          RAST._IType _out80;
          _out80 = (this).GenType(_1313_typeArg, DCOMP.GenTypeContext.@default());
          _1315_rTypeArg = _out80;
          _1310_types = Dafny.Sequence<RAST._IType>.Concat(_1310_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1315_rTypeArg))));
          if (((_1311_typeI) < (new BigInteger((_1268_variances).Count))) && (((_1268_variances).Select(_1311_typeI)).is_Nonvariant)) {
            _1304_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1304_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1315_rTypeArg));
            goto continue0;
          }
          DAST._ITypeArgDecl _1316_coerceTypeParam;
          DAST._ITypeArgDecl _1317_dt__update__tmp_h0 = _1312_typeParam;
          Dafny.ISequence<Dafny.Rune> _1318_dt__update_hname_h0 = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_1311_typeI));
          _1316_coerceTypeParam = DAST.TypeArgDecl.create(_1318_dt__update_hname_h0, (_1317_dt__update__tmp_h0).dtor_bounds, (_1317_dt__update__tmp_h0).dtor_variance);
          DAST._IType _1319_coerceTypeArg;
          RAST._ITypeParamDecl _1320_rCoerceTypeParamDecl;
          DAST._IType _out81;
          RAST._ITypeParamDecl _out82;
          (this).GenTypeParam(_1316_coerceTypeParam, out _out81, out _out82);
          _1319_coerceTypeArg = _out81;
          _1320_rCoerceTypeParamDecl = _out82;
          _1307_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_1307_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_1313_typeArg, _1319_coerceTypeArg)));
          RAST._IType _1321_rCoerceType;
          RAST._IType _out83;
          _out83 = (this).GenType(_1319_coerceTypeArg, DCOMP.GenTypeContext.@default());
          _1321_rCoerceType = _out83;
          _1308_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_1308_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_1315_rTypeArg, _1321_rCoerceType)));
          _1304_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1304_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1321_rCoerceType));
          _1305_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1305_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1320_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _1322_coerceFormal;
          _1322_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_1311_typeI));
          _1309_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_1309_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_1315_rTypeArg, _1321_rCoerceType), (RAST.Expr.create_Identifier(_1322_coerceFormal)).Clone())));
          _1306_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_1306_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1322_coerceFormal, RAST.__default.Rc(RAST.Type.create_IntersectionType(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_1315_rTypeArg), _1321_rCoerceType)), RAST.__default.StaticTrait)))));
        continue0: ;
        }
      after0: ;
        _1267_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1267_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1323_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1323_tpe);
})), _1310_types)))));
      }
      bool _1324_cIsEq;
      _1324_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_1324_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _1266_datatypeName, _1264_rTypeParamsDecls, _1267_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1264_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1266_datatypeName), _1263_rTypeParams), _1265_whereConstraints, _1282_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1325_printImplBodyCases;
      _1325_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1326_hashImplBodyCases;
      _1326_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1327_coerceImplBodyCases;
      _1327_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi20 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1328_i = BigInteger.Zero; _1328_i < _hi20; _1328_i++) {
        DAST._IDatatypeCtor _1329_ctor;
        _1329_ctor = ((c).dtor_ctors).Select(_1328_i);
        Dafny.ISequence<Dafny.Rune> _1330_ctorMatch;
        _1330_ctorMatch = DCOMP.__default.escapeName((_1329_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1331_modulePrefix;
        if (((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) {
          _1331_modulePrefix = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        } else {
          _1331_modulePrefix = Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."));
        }
        Dafny.ISequence<Dafny.Rune> _1332_ctorName;
        _1332_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1331_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1329_ctor).dtor_name));
        if (((new BigInteger((_1332_ctorName).Count)) >= (new BigInteger(13))) && (((_1332_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1332_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1333_printRhs;
        _1333_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1332_ctorName), (((_1329_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1334_hashRhs;
        _1334_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        Dafny.ISequence<RAST._IAssignIdentifier> _1335_coerceRhsArgs;
        _1335_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _1336_isNumeric;
        _1336_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1337_ctorMatchInner;
        _1337_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi21 = new BigInteger(((_1329_ctor).dtor_args).Count);
        for (BigInteger _1338_j = BigInteger.Zero; _1338_j < _hi21; _1338_j++) {
          DAST._IDatatypeDtor _1339_dtor;
          _1339_dtor = ((_1329_ctor).dtor_args).Select(_1338_j);
          Dafny.ISequence<Dafny.Rune> _1340_patternName;
          _1340_patternName = DCOMP.__default.escapeDtor(((_1339_dtor).dtor_formal).dtor_name);
          Dafny.ISequence<Dafny.Rune> _1341_fieldName;
          _1341_fieldName = DCOMP.__default.escapeField(((_1339_dtor).dtor_formal).dtor_name);
          DAST._IType _1342_formalType;
          _1342_formalType = ((_1339_dtor).dtor_formal).dtor_typ;
          if (((_1338_j).Sign == 0) && ((_1341_fieldName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1336_isNumeric = true;
          }
          if (_1336_isNumeric) {
            _1341_fieldName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1339_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1338_j)));
          }
          if ((_1342_formalType).is_Arrow) {
            _1334_hashRhs = (_1334_hashRhs).Then(((RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))));
          } else {
            _1334_hashRhs = (_1334_hashRhs).Then(((RAST.Expr.create_Identifier(_1341_fieldName)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))));
          }
          _1337_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1337_ctorMatchInner, ((_1336_isNumeric) ? (_1341_fieldName) : (_1340_patternName))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1338_j).Sign == 1) {
            _1333_printRhs = (_1333_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1333_printRhs = (_1333_printRhs).Then(RAST.Expr.create_RawExpr((((_1342_formalType).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \"<function>\")?")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1341_fieldName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))))));
          RAST._IExpr _1343_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _1344_formalTpe;
          RAST._IType _out84;
          _out84 = (this).GenType(_1342_formalType, DCOMP.GenTypeContext.@default());
          _1344_formalTpe = _out84;
          DAST._IType _1345_newFormalType;
          _1345_newFormalType = (_1342_formalType).Replace(_1307_coerceMap);
          RAST._IType _1346_newFormalTpe;
          _1346_newFormalTpe = (_1344_formalTpe).Replace(_1308_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1347_upcastConverter;
          _1347_upcastConverter = (this).UpcastConversionLambda(_1342_formalType, _1344_formalTpe, _1345_newFormalType, _1346_newFormalTpe, _1309_coerceMapToArg);
          if ((_1347_upcastConverter).is_Success) {
            RAST._IExpr _1348_coercionFunction;
            _1348_coercionFunction = (_1347_upcastConverter).dtor_value;
            _1343_coerceRhsArg = (_1348_coercionFunction).Apply1(RAST.Expr.create_Identifier(_1340_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_1338_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _1266_datatypeName));
            _1343_coerceRhsArg = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("todo!"))).Apply1(RAST.Expr.create_LiteralString((this.error).dtor_value, false, false));
          }
          _1335_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1335_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1340_patternName, _1343_coerceRhsArg)));
        }
        RAST._IExpr _1349_coerceRhs;
        _1349_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_1266_datatypeName)).MSel(DCOMP.__default.escapeName((_1329_ctor).dtor_name)), _1335_coerceRhsArgs);
        if (_1336_isNumeric) {
          _1330_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1330_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1337_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1330_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1330_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1337_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1329_ctor).dtor_hasAnyArgs) {
          _1333_printRhs = (_1333_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1333_printRhs = (_1333_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1325_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1325_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1266_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1330_ctorMatch), RAST.Expr.create_Block(_1333_printRhs))));
        _1326_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1326_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1266_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1330_ctorMatch), RAST.Expr.create_Block(_1334_hashRhs))));
        _1327_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1327_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1266_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1330_ctorMatch), RAST.Expr.create_Block(_1349_coerceRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IMatchCase> _1350_extraCases;
        _1350_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1266_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{"), (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}")))));
        _1325_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1325_printImplBodyCases, _1350_extraCases);
        _1326_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1326_hashImplBodyCases, _1350_extraCases);
        _1327_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1327_coerceImplBodyCases, _1350_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1351_defaultConstrainedTypeParams;
      _1351_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1264_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1352_rTypeParamsDeclsWithEq;
      _1352_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1264_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1353_rTypeParamsDeclsWithHash;
      _1353_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1264_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1354_printImplBody;
      _1354_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1325_printImplBodyCases);
      RAST._IExpr _1355_hashImplBody;
      _1355_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1326_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1264_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1266_datatypeName), _1263_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1264_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1266_datatypeName), _1263_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1354_printImplBody))))))));
      if ((new BigInteger((_1305_rCoerceTypeParams).Count)).Sign == 1) {
        RAST._IExpr _1356_coerceImplBody;
        _1356_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _1327_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1264_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1266_datatypeName), _1263_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), _1305_rCoerceTypeParams, _1306_coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1266_datatypeName), _1263_rTypeParams)), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1266_datatypeName), _1304_coerceTypes))))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.RcNew(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.Type.create_SelfOwned())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1266_datatypeName), _1304_coerceTypes)), _1356_coerceImplBody))))))))));
      }
      if (_1324_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1352_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1266_datatypeName), _1263_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1353_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1266_datatypeName), _1263_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1355_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1357_structName;
        _1357_structName = (RAST.Expr.create_Identifier(_1266_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1358_structAssignments;
        _1358_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi22 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1359_i = BigInteger.Zero; _1359_i < _hi22; _1359_i++) {
          DAST._IDatatypeDtor _1360_dtor;
          _1360_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1359_i);
          _1358_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1358_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1360_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1361_defaultConstrainedTypeParams;
        _1361_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1264_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1362_fullType;
        _1362_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1266_datatypeName), _1263_rTypeParams);
        if (_1324_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1361_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1362_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1362_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1357_structName, _1358_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1264_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_1362_fullType), RAST.Type.create_Borrowed(_1362_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
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
        BigInteger _hi23 = new BigInteger((p).Count);
        for (BigInteger _1363_i = BigInteger.Zero; _1363_i < _hi23; _1363_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1363_i))));
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
        BigInteger _hi24 = new BigInteger((p).Count);
        for (BigInteger _1364_i = BigInteger.Zero; _1364_i < _hi24; _1364_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1364_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, DCOMP._IGenTypeContext genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi25 = new BigInteger((args).Count);
      for (BigInteger _1365_i = BigInteger.Zero; _1365_i < _hi25; _1365_i++) {
        RAST._IType _1366_genTp;
        RAST._IType _out85;
        _out85 = (this).GenType((args).Select(_1365_i), genTypeContext);
        _1366_genTp = _out85;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1366_genTp));
      }
      return s;
    }
    public bool IsRcWrapped(Dafny.ISequence<DAST._IAttribute> attributes) {
      return ((!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("auto-nongrowing-size"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()))) && (!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false")))))) || ((attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true")))));
    }
    public RAST._IType GenType(DAST._IType c, DCOMP._IGenTypeContext genTypeContext)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source62 = c;
      {
        if (_source62.is_UserDefined) {
          DAST._IResolvedType _1367_resolved = _source62.dtor_resolved;
          {
            RAST._IType _1368_t;
            RAST._IType _out86;
            _out86 = DCOMP.COMP.GenPath((_1367_resolved).dtor_path);
            _1368_t = _out86;
            Dafny.ISequence<RAST._IType> _1369_typeArgs;
            Dafny.ISequence<RAST._IType> _out87;
            _out87 = (this).GenTypeArgs((_1367_resolved).dtor_typeArgs, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let9_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let9_0, _1370_dt__update__tmp_h0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let10_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let10_0, _1371_dt__update_hforTraitParents_h0 => DCOMP.GenTypeContext.create((_1370_dt__update__tmp_h0).dtor_inBinding, (_1370_dt__update__tmp_h0).dtor_inFn, _1371_dt__update_hforTraitParents_h0))))));
            _1369_typeArgs = _out87;
            s = RAST.Type.create_TypeApp(_1368_t, _1369_typeArgs);
            DAST._IResolvedTypeBase _source63 = (_1367_resolved).dtor_kind;
            {
              if (_source63.is_Class) {
                {
                  s = (this).Object(s);
                }
                goto after_match10;
              }
            }
            {
              if (_source63.is_Datatype) {
                {
                  if ((this).IsRcWrapped((_1367_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
                goto after_match10;
              }
            }
            {
              if (_source63.is_Trait) {
                {
                  if (((_1367_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
                  }
                  if (!((genTypeContext).dtor_forTraitParents)) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
                goto after_match10;
              }
            }
            {
              DAST._IType _1372_t = _source63.dtor_baseType;
              DAST._INewtypeRange _1373_range = _source63.dtor_range;
              bool _1374_erased = _source63.dtor_erase;
              {
                if (_1374_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source64 = DCOMP.COMP.NewtypeToRustType(_1372_t, _1373_range);
                  {
                    if (_source64.is_Some) {
                      RAST._IType _1375_v = _source64.dtor_value;
                      s = _1375_v;
                      goto after_match11;
                    }
                  }
                  {
                  }
                after_match11: ;
                }
              }
            }
          after_match10: ;
          }
          goto after_match9;
        }
      }
      {
        if (_source62.is_Object) {
          {
            s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
            if (!((genTypeContext).dtor_forTraitParents)) {
              s = (this).Object(RAST.Type.create_DynType(s));
            }
          }
          goto after_match9;
        }
      }
      {
        if (_source62.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1376_types = _source62.dtor_Tuple_a0;
          {
            Dafny.ISequence<RAST._IType> _1377_args;
            _1377_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1378_i;
            _1378_i = BigInteger.Zero;
            while ((_1378_i) < (new BigInteger((_1376_types).Count))) {
              RAST._IType _1379_generated;
              RAST._IType _out88;
              _out88 = (this).GenType((_1376_types).Select(_1378_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let11_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let11_0, _1380_dt__update__tmp_h1 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let12_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let12_0, _1381_dt__update_hforTraitParents_h1 => DCOMP.GenTypeContext.create((_1380_dt__update__tmp_h1).dtor_inBinding, (_1380_dt__update__tmp_h1).dtor_inFn, _1381_dt__update_hforTraitParents_h1))))));
              _1379_generated = _out88;
              _1377_args = Dafny.Sequence<RAST._IType>.Concat(_1377_args, Dafny.Sequence<RAST._IType>.FromElements(_1379_generated));
              _1378_i = (_1378_i) + (BigInteger.One);
            }
            if ((new BigInteger((_1376_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) {
              s = RAST.Type.create_TupleType(_1377_args);
            } else {
              s = RAST.__default.SystemTupleType(_1377_args);
            }
          }
          goto after_match9;
        }
      }
      {
        if (_source62.is_Array) {
          DAST._IType _1382_element = _source62.dtor_element;
          BigInteger _1383_dims = _source62.dtor_dims;
          {
            if ((_1383_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1384_elem;
              RAST._IType _out89;
              _out89 = (this).GenType(_1382_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let13_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let13_0, _1385_dt__update__tmp_h2 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let14_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let14_0, _1386_dt__update_hforTraitParents_h2 => DCOMP.GenTypeContext.create((_1385_dt__update__tmp_h2).dtor_inBinding, (_1385_dt__update__tmp_h2).dtor_inFn, _1386_dt__update_hforTraitParents_h2))))));
              _1384_elem = _out89;
              if ((_1383_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1384_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1387_n;
                _1387_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1383_dims));
                s = ((RAST.__default.dafny__runtime__type).MSel(_1387_n)).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1384_elem));
                s = (this).Object(s);
              }
            }
          }
          goto after_match9;
        }
      }
      {
        if (_source62.is_Seq) {
          DAST._IType _1388_element = _source62.dtor_element;
          {
            RAST._IType _1389_elem;
            RAST._IType _out90;
            _out90 = (this).GenType(_1388_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let15_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let15_0, _1390_dt__update__tmp_h3 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let16_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let16_0, _1391_dt__update_hforTraitParents_h3 => DCOMP.GenTypeContext.create((_1390_dt__update__tmp_h3).dtor_inBinding, (_1390_dt__update__tmp_h3).dtor_inFn, _1391_dt__update_hforTraitParents_h3))))));
            _1389_elem = _out90;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1389_elem));
          }
          goto after_match9;
        }
      }
      {
        if (_source62.is_Set) {
          DAST._IType _1392_element = _source62.dtor_element;
          {
            RAST._IType _1393_elem;
            RAST._IType _out91;
            _out91 = (this).GenType(_1392_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let17_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let17_0, _1394_dt__update__tmp_h4 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let18_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let18_0, _1395_dt__update_hforTraitParents_h4 => DCOMP.GenTypeContext.create((_1394_dt__update__tmp_h4).dtor_inBinding, (_1394_dt__update__tmp_h4).dtor_inFn, _1395_dt__update_hforTraitParents_h4))))));
            _1393_elem = _out91;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1393_elem));
          }
          goto after_match9;
        }
      }
      {
        if (_source62.is_Multiset) {
          DAST._IType _1396_element = _source62.dtor_element;
          {
            RAST._IType _1397_elem;
            RAST._IType _out92;
            _out92 = (this).GenType(_1396_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let19_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let19_0, _1398_dt__update__tmp_h5 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let20_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let20_0, _1399_dt__update_hforTraitParents_h5 => DCOMP.GenTypeContext.create((_1398_dt__update__tmp_h5).dtor_inBinding, (_1398_dt__update__tmp_h5).dtor_inFn, _1399_dt__update_hforTraitParents_h5))))));
            _1397_elem = _out92;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1397_elem));
          }
          goto after_match9;
        }
      }
      {
        if (_source62.is_Map) {
          DAST._IType _1400_key = _source62.dtor_key;
          DAST._IType _1401_value = _source62.dtor_value;
          {
            RAST._IType _1402_keyType;
            RAST._IType _out93;
            _out93 = (this).GenType(_1400_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let21_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let21_0, _1403_dt__update__tmp_h6 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let22_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let22_0, _1404_dt__update_hforTraitParents_h6 => DCOMP.GenTypeContext.create((_1403_dt__update__tmp_h6).dtor_inBinding, (_1403_dt__update__tmp_h6).dtor_inFn, _1404_dt__update_hforTraitParents_h6))))));
            _1402_keyType = _out93;
            RAST._IType _1405_valueType;
            RAST._IType _out94;
            _out94 = (this).GenType(_1401_value, genTypeContext);
            _1405_valueType = _out94;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1402_keyType, _1405_valueType));
          }
          goto after_match9;
        }
      }
      {
        if (_source62.is_MapBuilder) {
          DAST._IType _1406_key = _source62.dtor_key;
          DAST._IType _1407_value = _source62.dtor_value;
          {
            RAST._IType _1408_keyType;
            RAST._IType _out95;
            _out95 = (this).GenType(_1406_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let23_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let23_0, _1409_dt__update__tmp_h7 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let24_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let24_0, _1410_dt__update_hforTraitParents_h7 => DCOMP.GenTypeContext.create((_1409_dt__update__tmp_h7).dtor_inBinding, (_1409_dt__update__tmp_h7).dtor_inFn, _1410_dt__update_hforTraitParents_h7))))));
            _1408_keyType = _out95;
            RAST._IType _1411_valueType;
            RAST._IType _out96;
            _out96 = (this).GenType(_1407_value, genTypeContext);
            _1411_valueType = _out96;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1408_keyType, _1411_valueType));
          }
          goto after_match9;
        }
      }
      {
        if (_source62.is_SetBuilder) {
          DAST._IType _1412_elem = _source62.dtor_element;
          {
            RAST._IType _1413_elemType;
            RAST._IType _out97;
            _out97 = (this).GenType(_1412_elem, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let25_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let25_0, _1414_dt__update__tmp_h8 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let26_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let26_0, _1415_dt__update_hforTraitParents_h8 => DCOMP.GenTypeContext.create((_1414_dt__update__tmp_h8).dtor_inBinding, (_1414_dt__update__tmp_h8).dtor_inFn, _1415_dt__update_hforTraitParents_h8))))));
            _1413_elemType = _out97;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1413_elemType));
          }
          goto after_match9;
        }
      }
      {
        if (_source62.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1416_args = _source62.dtor_args;
          DAST._IType _1417_result = _source62.dtor_result;
          {
            Dafny.ISequence<RAST._IType> _1418_argTypes;
            _1418_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1419_i;
            _1419_i = BigInteger.Zero;
            while ((_1419_i) < (new BigInteger((_1416_args).Count))) {
              RAST._IType _1420_generated;
              RAST._IType _out98;
              _out98 = (this).GenType((_1416_args).Select(_1419_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let27_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let27_0, _1421_dt__update__tmp_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let28_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let28_0, _1422_dt__update_hforTraitParents_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(true, _pat_let29_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let29_0, _1423_dt__update_hinFn_h0 => DCOMP.GenTypeContext.create((_1421_dt__update__tmp_h9).dtor_inBinding, _1423_dt__update_hinFn_h0, _1422_dt__update_hforTraitParents_h9))))))));
              _1420_generated = _out98;
              _1418_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1418_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1420_generated)));
              _1419_i = (_1419_i) + (BigInteger.One);
            }
            RAST._IType _1424_resultType;
            RAST._IType _out99;
            _out99 = (this).GenType(_1417_result, DCOMP.GenTypeContext.create(((genTypeContext).dtor_inFn) || ((genTypeContext).dtor_inBinding), false, false));
            _1424_resultType = _out99;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1418_argTypes, _1424_resultType)));
          }
          goto after_match9;
        }
      }
      {
        if (_source62.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source62.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1425_name = _h90;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1425_name));
          goto after_match9;
        }
      }
      {
        if (_source62.is_Primitive) {
          DAST._IPrimitive _1426_p = _source62.dtor_Primitive_a0;
          {
            DAST._IPrimitive _source65 = _1426_p;
            {
              if (_source65.is_Int) {
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
                goto after_match12;
              }
            }
            {
              if (_source65.is_Real) {
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
                goto after_match12;
              }
            }
            {
              if (_source65.is_String) {
                s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
                goto after_match12;
              }
            }
            {
              if (_source65.is_Bool) {
                s = RAST.Type.create_Bool();
                goto after_match12;
              }
            }
            {
              s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
            }
          after_match12: ;
          }
          goto after_match9;
        }
      }
      {
        Dafny.ISequence<Dafny.Rune> _1427_v = _source62.dtor_Passthrough_a0;
        s = RAST.__default.RawType(_1427_v);
      }
    after_match9: ;
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
      for (BigInteger _1428_i = BigInteger.Zero; _1428_i < _hi26; _1428_i++) {
        DAST._IMethod _source66 = (body).Select(_1428_i);
        {
          DAST._IMethod _1429_m = _source66;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source67 = (_1429_m).dtor_overridingPath;
            {
              if (_source67.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1430_p = _source67.dtor_value;
                {
                  Dafny.ISequence<RAST._IImplMember> _1431_existing;
                  _1431_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1430_p)) {
                    _1431_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1430_p);
                  }
                  if (((new BigInteger(((_1429_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _1432_genMethod;
                  RAST._IImplMember _out100;
                  _out100 = (this).GenMethod(_1429_m, true, enclosingType, enclosingTypeParams);
                  _1432_genMethod = _out100;
                  _1431_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1431_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1432_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1430_p, _1431_existing)));
                }
                goto after_match14;
              }
            }
            {
              {
                RAST._IImplMember _1433_generated;
                RAST._IImplMember _out101;
                _out101 = (this).GenMethod(_1429_m, forTrait, enclosingType, enclosingTypeParams);
                _1433_generated = _out101;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1433_generated));
              }
            }
          after_match14: ;
          }
        }
      after_match13: ;
      }
    }
    public Dafny.ISequence<RAST._IFormal> GenParams(Dafny.ISequence<DAST._IFormal> @params)
    {
      Dafny.ISequence<RAST._IFormal> s = Dafny.Sequence<RAST._IFormal>.Empty;
      s = Dafny.Sequence<RAST._IFormal>.FromElements();
      BigInteger _hi27 = new BigInteger((@params).Count);
      for (BigInteger _1434_i = BigInteger.Zero; _1434_i < _hi27; _1434_i++) {
        DAST._IFormal _1435_param;
        _1435_param = (@params).Select(_1434_i);
        RAST._IType _1436_paramType;
        RAST._IType _out102;
        _out102 = (this).GenType((_1435_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _1436_paramType = _out102;
        if ((!((_1436_paramType).CanReadWithoutClone())) && (!((_1435_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1436_paramType = RAST.Type.create_Borrowed(_1436_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_1435_param).dtor_name), _1436_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1437_params;
      Dafny.ISequence<RAST._IFormal> _out103;
      _out103 = (this).GenParams((m).dtor_params);
      _1437_params = _out103;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1438_paramNames;
      _1438_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1439_paramTypes;
      _1439_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi28 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1440_paramI = BigInteger.Zero; _1440_paramI < _hi28; _1440_paramI++) {
        DAST._IFormal _1441_dafny__formal;
        _1441_dafny__formal = ((m).dtor_params).Select(_1440_paramI);
        RAST._IFormal _1442_formal;
        _1442_formal = (_1437_params).Select(_1440_paramI);
        Dafny.ISequence<Dafny.Rune> _1443_name;
        _1443_name = (_1442_formal).dtor_name;
        _1438_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1438_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1443_name));
        _1439_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1439_paramTypes, _1443_name, (_1442_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1444_fnName;
      _1444_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _1445_selfIdent;
      _1445_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1446_selfId;
        _1446_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((m).dtor_outVarsAreUninitFieldsToAssign) {
          _1446_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv2 = enclosingTypeParams;
        DAST._IType _1447_instanceType;
        DAST._IType _source68 = enclosingType;
        {
          if (_source68.is_UserDefined) {
            DAST._IResolvedType _1448_r = _source68.dtor_resolved;
            _1447_instanceType = DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_1448_r, _pat_let30_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let30_0, _1449_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv2, _pat_let31_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let31_0, _1450_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_1449_dt__update__tmp_h0).dtor_path, _1450_dt__update_htypeArgs_h0, (_1449_dt__update__tmp_h0).dtor_kind, (_1449_dt__update__tmp_h0).dtor_attributes, (_1449_dt__update__tmp_h0).dtor_properMethods, (_1449_dt__update__tmp_h0).dtor_extendedTypes))))));
            goto after_match15;
          }
        }
        {
          _1447_instanceType = enclosingType;
        }
      after_match15: ;
        if (forTrait) {
          RAST._IFormal _1451_selfFormal;
          if ((m).dtor_wasFunction) {
            _1451_selfFormal = RAST.Formal.selfBorrowed;
          } else {
            _1451_selfFormal = RAST.Formal.selfBorrowedMut;
          }
          _1437_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1451_selfFormal), _1437_params);
        } else {
          RAST._IType _1452_tpe;
          RAST._IType _out104;
          _out104 = (this).GenType(_1447_instanceType, DCOMP.GenTypeContext.@default());
          _1452_tpe = _out104;
          if ((_1446_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            _1452_tpe = RAST.Type.create_Borrowed(_1452_tpe);
          } else if ((_1446_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_1452_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _1452_tpe = RAST.__default.SelfBorrowed;
              } else {
                _1452_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              if ((((enclosingType).is_UserDefined) && ((((enclosingType).dtor_resolved).dtor_kind).is_Datatype)) && ((this).IsRcWrapped(((enclosingType).dtor_resolved).dtor_attributes))) {
                _1452_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.Type.create_SelfOwned()));
              } else {
                _1452_tpe = RAST.Type.create_Borrowed(RAST.Type.create_SelfOwned());
              }
            }
          }
          _1437_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1446_selfId, _1452_tpe)), _1437_params);
        }
        _1445_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_1446_selfId, _1447_instanceType);
      }
      Dafny.ISequence<RAST._IType> _1453_retTypeArgs;
      _1453_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1454_typeI;
      _1454_typeI = BigInteger.Zero;
      while ((_1454_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1455_typeExpr;
        RAST._IType _out105;
        _out105 = (this).GenType(((m).dtor_outTypes).Select(_1454_typeI), DCOMP.GenTypeContext.@default());
        _1455_typeExpr = _out105;
        _1453_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1453_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1455_typeExpr));
        _1454_typeI = (_1454_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1456_visibility;
      if (forTrait) {
        _1456_visibility = RAST.Visibility.create_PRIV();
      } else {
        _1456_visibility = RAST.Visibility.create_PUB();
      }
      Dafny.ISequence<DAST._ITypeArgDecl> _1457_typeParamsFiltered;
      _1457_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi29 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1458_typeParamI = BigInteger.Zero; _1458_typeParamI < _hi29; _1458_typeParamI++) {
        DAST._ITypeArgDecl _1459_typeParam;
        _1459_typeParam = ((m).dtor_typeParams).Select(_1458_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1459_typeParam).dtor_name)))) {
          _1457_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1457_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1459_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1460_typeParams;
      _1460_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1457_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi30 = new BigInteger((_1457_typeParamsFiltered).Count);
        for (BigInteger _1461_i = BigInteger.Zero; _1461_i < _hi30; _1461_i++) {
          DAST._IType _1462_typeArg;
          RAST._ITypeParamDecl _1463_rTypeParamDecl;
          DAST._IType _out106;
          RAST._ITypeParamDecl _out107;
          (this).GenTypeParam((_1457_typeParamsFiltered).Select(_1461_i), out _out106, out _out107);
          _1462_typeArg = _out106;
          _1463_rTypeParamDecl = _out107;
          RAST._ITypeParamDecl _1464_dt__update__tmp_h1 = _1463_rTypeParamDecl;
          Dafny.ISequence<RAST._IType> _1465_dt__update_hconstraints_h0 = Dafny.Sequence<RAST._IType>.Concat((_1463_rTypeParamDecl).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
          _1463_rTypeParamDecl = RAST.TypeParamDecl.create((_1464_dt__update__tmp_h1).dtor_content, _1465_dt__update_hconstraints_h0);
          _1460_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1460_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1463_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1466_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1467_env = DCOMP.Environment.Default();
      RAST._IExpr _1468_preBody;
      _1468_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1469_preAssignNames;
      _1469_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1470_preAssignTypes;
      _1470_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1471_earlyReturn;
        _1471_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None();
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source69 = (m).dtor_outVars;
        {
          if (_source69.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1472_outVars = _source69.dtor_value;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1471_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
                BigInteger _hi31 = new BigInteger((_1472_outVars).Count);
                for (BigInteger _1473_outI = BigInteger.Zero; _1473_outI < _hi31; _1473_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1474_outVar;
                  _1474_outVar = (_1472_outVars).Select(_1473_outI);
                  Dafny.ISequence<Dafny.Rune> _1475_outName;
                  _1475_outName = DCOMP.__default.escapeName((_1474_outVar));
                  Dafny.ISequence<Dafny.Rune> _1476_tracker__name;
                  _1476_tracker__name = DCOMP.__default.AddAssignedPrefix(_1475_outName);
                  _1469_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1469_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1476_tracker__name));
                  _1470_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1470_preAssignTypes, _1476_tracker__name, RAST.Type.create_Bool());
                  _1468_preBody = (_1468_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1476_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1477_tupleArgs;
                _1477_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
                BigInteger _hi32 = new BigInteger((_1472_outVars).Count);
                for (BigInteger _1478_outI = BigInteger.Zero; _1478_outI < _hi32; _1478_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1479_outVar;
                  _1479_outVar = (_1472_outVars).Select(_1478_outI);
                  RAST._IType _1480_outType;
                  RAST._IType _out108;
                  _out108 = (this).GenType(((m).dtor_outTypes).Select(_1478_outI), DCOMP.GenTypeContext.@default());
                  _1480_outType = _out108;
                  Dafny.ISequence<Dafny.Rune> _1481_outName;
                  _1481_outName = DCOMP.__default.escapeName((_1479_outVar));
                  _1438_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1438_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1481_outName));
                  RAST._IType _1482_outMaybeType;
                  if ((_1480_outType).CanReadWithoutClone()) {
                    _1482_outMaybeType = _1480_outType;
                  } else {
                    _1482_outMaybeType = RAST.__default.MaybePlaceboType(_1480_outType);
                  }
                  _1439_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1439_paramTypes, _1481_outName, _1482_outMaybeType);
                  _1477_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1477_tupleArgs, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1481_outName));
                }
                _1471_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(_1477_tupleArgs);
              }
            }
            goto after_match16;
          }
        }
        {
        }
      after_match16: ;
        _1467_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1469_preAssignNames, _1438_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1470_preAssignTypes, _1439_paramTypes));
        RAST._IExpr _1483_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1484___v69;
        DCOMP._IEnvironment _1485___v70;
        RAST._IExpr _out109;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out110;
        DCOMP._IEnvironment _out111;
        (this).GenStmts((m).dtor_body, _1445_selfIdent, _1467_env, true, _1471_earlyReturn, out _out109, out _out110, out _out111);
        _1483_body = _out109;
        _1484___v69 = _out110;
        _1485___v70 = _out111;
        _1466_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1468_preBody).Then(_1483_body));
      } else {
        _1467_env = DCOMP.Environment.create(_1438_paramNames, _1439_paramTypes);
        _1466_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1456_visibility, RAST.Fn.create(_1444_fnName, _1460_typeParams, _1437_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1453_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1453_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1453_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1466_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1486_declarations;
      _1486_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1487_i;
      _1487_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1488_stmts;
      _1488_stmts = stmts;
      while ((_1487_i) < (new BigInteger((_1488_stmts).Count))) {
        DAST._IStatement _1489_stmt;
        _1489_stmt = (_1488_stmts).Select(_1487_i);
        DAST._IStatement _source70 = _1489_stmt;
        {
          if (_source70.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1490_name = _source70.dtor_name;
            DAST._IType _1491_optType = _source70.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source70.dtor_maybeValue;
            if (maybeValue0.is_None) {
              if (((_1487_i) + (BigInteger.One)) < (new BigInteger((_1488_stmts).Count))) {
                DAST._IStatement _source71 = (_1488_stmts).Select((_1487_i) + (BigInteger.One));
                {
                  if (_source71.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source71.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> ident0 = lhs0.dtor_ident;
                      Dafny.ISequence<Dafny.Rune> _1492_name2 = ident0;
                      DAST._IExpression _1493_rhs = _source71.dtor_value;
                      if (object.Equals(_1492_name2, _1490_name)) {
                        _1488_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1488_stmts).Subsequence(BigInteger.Zero, _1487_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1490_name, _1491_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1493_rhs)))), (_1488_stmts).Drop((_1487_i) + (new BigInteger(2))));
                        _1489_stmt = (_1488_stmts).Select(_1487_i);
                      }
                      goto after_match18;
                    }
                  }
                }
                {
                }
              after_match18: ;
              }
              goto after_match17;
            }
          }
        }
        {
        }
      after_match17: ;
        RAST._IExpr _1494_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1495_recIdents;
        DCOMP._IEnvironment _1496_newEnv2;
        RAST._IExpr _out112;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out113;
        DCOMP._IEnvironment _out114;
        (this).GenStmt(_1489_stmt, selfIdent, newEnv, (isLast) && ((_1487_i) == ((new BigInteger((_1488_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out112, out _out113, out _out114);
        _1494_stmtExpr = _out112;
        _1495_recIdents = _out113;
        _1496_newEnv2 = _out114;
        newEnv = _1496_newEnv2;
        DAST._IStatement _source72 = _1489_stmt;
        {
          if (_source72.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1497_name = _source72.dtor_name;
            {
              _1486_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1486_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_1497_name)));
            }
            goto after_match19;
          }
        }
        {
        }
      after_match19: ;
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1495_recIdents, _1486_declarations));
        generated = (generated).Then(_1494_stmtExpr);
        _1487_i = (_1487_i) + (BigInteger.One);
        if ((_1494_stmtExpr).is_Return) {
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
      DAST._IAssignLhs _source73 = lhs;
      {
        if (_source73.is_Ident) {
          Dafny.ISequence<Dafny.Rune> ident1 = _source73.dtor_ident;
          Dafny.ISequence<Dafny.Rune> _1498_id = ident1;
          {
            Dafny.ISequence<Dafny.Rune> _1499_idRust;
            _1499_idRust = DCOMP.__default.escapeName(_1498_id);
            if (((env).IsBorrowed(_1499_idRust)) || ((env).IsBorrowedMut(_1499_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1499_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1499_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1499_idRust);
            needsIIFE = false;
          }
          goto after_match20;
        }
      }
      {
        if (_source73.is_Select) {
          DAST._IExpression _1500_on = _source73.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1501_field = _source73.dtor_field;
          {
            Dafny.ISequence<Dafny.Rune> _1502_fieldName;
            _1502_fieldName = DCOMP.__default.escapeName(_1501_field);
            RAST._IExpr _1503_onExpr;
            DCOMP._IOwnership _1504_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1505_recIdents;
            RAST._IExpr _out115;
            DCOMP._IOwnership _out116;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out117;
            (this).GenExpr(_1500_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out115, out _out116, out _out117);
            _1503_onExpr = _out115;
            _1504_onOwned = _out116;
            _1505_recIdents = _out117;
            RAST._IExpr _source74 = _1503_onExpr;
            {
              bool disjunctiveMatch10 = false;
              if (_source74.is_Call) {
                RAST._IExpr obj2 = _source74.dtor_obj;
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
              if (_source74.is_Identifier) {
                Dafny.ISequence<Dafny.Rune> name13 = _source74.dtor_name;
                if (object.Equals(name13, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                  disjunctiveMatch10 = true;
                }
              }
              if (_source74.is_UnaryOp) {
                Dafny.ISequence<Dafny.Rune> op14 = _source74.dtor_op1;
                if (object.Equals(op14, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                  RAST._IExpr underlying4 = _source74.dtor_underlying;
                  if (underlying4.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name14 = underlying4.dtor_name;
                    if (object.Equals(name14, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      disjunctiveMatch10 = true;
                    }
                  }
                }
              }
              if (disjunctiveMatch10) {
                Dafny.ISequence<Dafny.Rune> _1506_isAssignedVar;
                _1506_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1502_fieldName);
                if (((newEnv).dtor_names).Contains(_1506_isAssignedVar)) {
                  generated = ((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1502_fieldName), RAST.Expr.create_Identifier(_1506_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1506_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _1506_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _1502_fieldName, rhs);
                }
                goto after_match21;
              }
            }
            {
              if (!object.Equals(_1503_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _1503_onExpr = ((this).modify__macro).Apply1(_1503_onExpr);
              }
              generated = RAST.__default.AssignMember(_1503_onExpr, _1502_fieldName, rhs);
            }
          after_match21: ;
            readIdents = _1505_recIdents;
            needsIIFE = false;
          }
          goto after_match20;
        }
      }
      {
        DAST._IExpression _1507_on = _source73.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1508_indices = _source73.dtor_indices;
        {
          RAST._IExpr _1509_onExpr;
          DCOMP._IOwnership _1510_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1511_recIdents;
          RAST._IExpr _out118;
          DCOMP._IOwnership _out119;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out120;
          (this).GenExpr(_1507_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out118, out _out119, out _out120);
          _1509_onExpr = _out118;
          _1510_onOwned = _out119;
          _1511_recIdents = _out120;
          readIdents = _1511_recIdents;
          _1509_onExpr = ((this).modify__macro).Apply1(_1509_onExpr);
          RAST._IExpr _1512_r;
          _1512_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1513_indicesExpr;
          _1513_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi33 = new BigInteger((_1508_indices).Count);
          for (BigInteger _1514_i = BigInteger.Zero; _1514_i < _hi33; _1514_i++) {
            RAST._IExpr _1515_idx;
            DCOMP._IOwnership _1516___v79;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1517_recIdentsIdx;
            RAST._IExpr _out121;
            DCOMP._IOwnership _out122;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out123;
            (this).GenExpr((_1508_indices).Select(_1514_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out121, out _out122, out _out123);
            _1515_idx = _out121;
            _1516___v79 = _out122;
            _1517_recIdentsIdx = _out123;
            Dafny.ISequence<Dafny.Rune> _1518_varName;
            _1518_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1514_i));
            _1513_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1513_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1518_varName)));
            _1512_r = (_1512_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1518_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.IntoUsize(_1515_idx))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1517_recIdentsIdx);
          }
          if ((new BigInteger((_1508_indices).Count)) > (BigInteger.One)) {
            _1509_onExpr = (_1509_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1519_rhs;
          _1519_rhs = rhs;
          var _pat_let_tv3 = env;
          if (((_1509_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1509_onExpr).LhsIdentifierName(), _pat_let32_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let32_0, _1520_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv3).GetType(_1520_name), _pat_let33_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let33_0, _1521_tpe => ((_1521_tpe).is_Some) && (((_1521_tpe).dtor_value).IsUninitArray())))))))) {
            _1519_rhs = RAST.__default.MaybeUninitNew(_1519_rhs);
          }
          generated = (_1512_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1509_onExpr, _1513_indicesExpr)), _1519_rhs));
          needsIIFE = true;
        }
      }
    after_match20: ;
    }
    public void GenStmt(DAST._IStatement stmt, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source75 = stmt;
      {
        if (_source75.is_ConstructorNewSeparator) {
          Dafny.ISequence<DAST._IFormal> _1522_fields = _source75.dtor_fields;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi34 = new BigInteger((_1522_fields).Count);
            for (BigInteger _1523_i = BigInteger.Zero; _1523_i < _hi34; _1523_i++) {
              DAST._IFormal _1524_field;
              _1524_field = (_1522_fields).Select(_1523_i);
              Dafny.ISequence<Dafny.Rune> _1525_fieldName;
              _1525_fieldName = DCOMP.__default.escapeName((_1524_field).dtor_name);
              RAST._IType _1526_fieldTyp;
              RAST._IType _out124;
              _out124 = (this).GenType((_1524_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _1526_fieldTyp = _out124;
              Dafny.ISequence<Dafny.Rune> _1527_isAssignedVar;
              _1527_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1525_fieldName);
              if (((newEnv).dtor_names).Contains(_1527_isAssignedVar)) {
                RAST._IExpr _1528_rhs;
                DCOMP._IOwnership _1529___v80;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1530___v81;
                RAST._IExpr _out125;
                DCOMP._IOwnership _out126;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out127;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1524_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out125, out _out126, out _out127);
                _1528_rhs = _out125;
                _1529___v80 = _out126;
                _1530___v81 = _out127;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1527_isAssignedVar));
                generated = (generated).Then(((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1525_fieldName), RAST.Expr.create_Identifier(_1527_isAssignedVar), _1528_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1527_isAssignedVar);
              }
            }
          }
          goto after_match22;
        }
      }
      {
        if (_source75.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1531_name = _source75.dtor_name;
          DAST._IType _1532_typ = _source75.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source75.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1533_expression = maybeValue1.dtor_value;
            {
              RAST._IType _1534_tpe;
              RAST._IType _out128;
              _out128 = (this).GenType(_1532_typ, DCOMP.GenTypeContext.InBinding());
              _1534_tpe = _out128;
              Dafny.ISequence<Dafny.Rune> _1535_varName;
              _1535_varName = DCOMP.__default.escapeName(_1531_name);
              bool _1536_hasCopySemantics;
              _1536_hasCopySemantics = (_1534_tpe).CanReadWithoutClone();
              if (((_1533_expression).is_InitializationValue) && (!(_1536_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1535_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).ApplyType1(_1534_tpe)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1535_varName, RAST.__default.MaybePlaceboType(_1534_tpe));
              } else {
                RAST._IExpr _1537_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1538_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1533_expression).is_InitializationValue) && ((_1534_tpe).IsObjectOrPointer())) {
                  _1537_expr = (_1534_tpe).ToNullExpr();
                  _1538_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1539_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out129;
                  DCOMP._IOwnership _out130;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
                  (this).GenExpr(_1533_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out129, out _out130, out _out131);
                  _1537_expr = _out129;
                  _1539_exprOwnership = _out130;
                  _1538_recIdents = _out131;
                }
                readIdents = _1538_recIdents;
                if ((_1533_expression).is_NewUninitArray) {
                  _1534_tpe = (_1534_tpe).TypeAtInitialization();
                } else {
                  _1534_tpe = _1534_tpe;
                }
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_1531_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1534_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1537_expr));
                newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_1531_name), _1534_tpe);
              }
            }
            goto after_match22;
          }
        }
      }
      {
        if (_source75.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1540_name = _source75.dtor_name;
          DAST._IType _1541_typ = _source75.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source75.dtor_maybeValue;
          if (maybeValue2.is_None) {
            {
              DAST._IStatement _1542_newStmt;
              _1542_newStmt = DAST.Statement.create_DeclareVar(_1540_name, _1541_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1541_typ)));
              RAST._IExpr _out132;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out133;
              DCOMP._IEnvironment _out134;
              (this).GenStmt(_1542_newStmt, selfIdent, env, isLast, earlyReturn, out _out132, out _out133, out _out134);
              generated = _out132;
              readIdents = _out133;
              newEnv = _out134;
            }
            goto after_match22;
          }
        }
      }
      {
        if (_source75.is_Assign) {
          DAST._IAssignLhs _1543_lhs = _source75.dtor_lhs;
          DAST._IExpression _1544_expression = _source75.dtor_value;
          {
            RAST._IExpr _1545_exprGen;
            DCOMP._IOwnership _1546___v82;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1547_exprIdents;
            RAST._IExpr _out135;
            DCOMP._IOwnership _out136;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
            (this).GenExpr(_1544_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out135, out _out136, out _out137);
            _1545_exprGen = _out135;
            _1546___v82 = _out136;
            _1547_exprIdents = _out137;
            if ((_1543_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1548_rustId;
              _1548_rustId = DCOMP.__default.escapeName(((_1543_lhs).dtor_ident));
              Std.Wrappers._IOption<RAST._IType> _1549_tpe;
              _1549_tpe = (env).GetType(_1548_rustId);
              if (((_1549_tpe).is_Some) && ((((_1549_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1545_exprGen = RAST.__default.MaybePlacebo(_1545_exprGen);
              }
            }
            if (((_1543_lhs).is_Index) && (((_1543_lhs).dtor_expr).is_Ident)) {
              Dafny.ISequence<Dafny.Rune> _1550_rustId;
              _1550_rustId = DCOMP.__default.escapeName(((_1543_lhs).dtor_expr).dtor_name);
              Std.Wrappers._IOption<RAST._IType> _1551_tpe;
              _1551_tpe = (env).GetType(_1550_rustId);
              if (((_1551_tpe).is_Some) && ((((_1551_tpe).dtor_value).ExtractMaybeUninitArrayElement()).is_Some)) {
                _1545_exprGen = RAST.__default.MaybeUninitNew(_1545_exprGen);
              }
            }
            RAST._IExpr _1552_lhsGen;
            bool _1553_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1554_recIdents;
            DCOMP._IEnvironment _1555_resEnv;
            RAST._IExpr _out138;
            bool _out139;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out140;
            DCOMP._IEnvironment _out141;
            (this).GenAssignLhs(_1543_lhs, _1545_exprGen, selfIdent, env, out _out138, out _out139, out _out140, out _out141);
            _1552_lhsGen = _out138;
            _1553_needsIIFE = _out139;
            _1554_recIdents = _out140;
            _1555_resEnv = _out141;
            generated = _1552_lhsGen;
            newEnv = _1555_resEnv;
            if (_1553_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1554_recIdents, _1547_exprIdents);
          }
          goto after_match22;
        }
      }
      {
        if (_source75.is_If) {
          DAST._IExpression _1556_cond = _source75.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1557_thnDafny = _source75.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1558_elsDafny = _source75.dtor_els;
          {
            RAST._IExpr _1559_cond;
            DCOMP._IOwnership _1560___v83;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1561_recIdents;
            RAST._IExpr _out142;
            DCOMP._IOwnership _out143;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
            (this).GenExpr(_1556_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out142, out _out143, out _out144);
            _1559_cond = _out142;
            _1560___v83 = _out143;
            _1561_recIdents = _out144;
            Dafny.ISequence<Dafny.Rune> _1562_condString;
            _1562_condString = (_1559_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1561_recIdents;
            RAST._IExpr _1563_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1564_thnIdents;
            DCOMP._IEnvironment _1565_thnEnv;
            RAST._IExpr _out145;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out146;
            DCOMP._IEnvironment _out147;
            (this).GenStmts(_1557_thnDafny, selfIdent, env, isLast, earlyReturn, out _out145, out _out146, out _out147);
            _1563_thn = _out145;
            _1564_thnIdents = _out146;
            _1565_thnEnv = _out147;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1564_thnIdents);
            RAST._IExpr _1566_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1567_elsIdents;
            DCOMP._IEnvironment _1568_elsEnv;
            RAST._IExpr _out148;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out149;
            DCOMP._IEnvironment _out150;
            (this).GenStmts(_1558_elsDafny, selfIdent, env, isLast, earlyReturn, out _out148, out _out149, out _out150);
            _1566_els = _out148;
            _1567_elsIdents = _out149;
            _1568_elsEnv = _out150;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1567_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1559_cond, _1563_thn, _1566_els);
          }
          goto after_match22;
        }
      }
      {
        if (_source75.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1569_lbl = _source75.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1570_body = _source75.dtor_body;
          {
            RAST._IExpr _1571_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1572_bodyIdents;
            DCOMP._IEnvironment _1573_env2;
            RAST._IExpr _out151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out152;
            DCOMP._IEnvironment _out153;
            (this).GenStmts(_1570_body, selfIdent, env, isLast, earlyReturn, out _out151, out _out152, out _out153);
            _1571_body = _out151;
            _1572_bodyIdents = _out152;
            _1573_env2 = _out153;
            readIdents = _1572_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1569_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1571_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
          goto after_match22;
        }
      }
      {
        if (_source75.is_While) {
          DAST._IExpression _1574_cond = _source75.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1575_body = _source75.dtor_body;
          {
            RAST._IExpr _1576_cond;
            DCOMP._IOwnership _1577___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1578_recIdents;
            RAST._IExpr _out154;
            DCOMP._IOwnership _out155;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
            (this).GenExpr(_1574_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out154, out _out155, out _out156);
            _1576_cond = _out154;
            _1577___v84 = _out155;
            _1578_recIdents = _out156;
            readIdents = _1578_recIdents;
            RAST._IExpr _1579_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1580_bodyIdents;
            DCOMP._IEnvironment _1581_bodyEnv;
            RAST._IExpr _out157;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out158;
            DCOMP._IEnvironment _out159;
            (this).GenStmts(_1575_body, selfIdent, env, false, earlyReturn, out _out157, out _out158, out _out159);
            _1579_bodyExpr = _out157;
            _1580_bodyIdents = _out158;
            _1581_bodyEnv = _out159;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1580_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1576_cond), _1579_bodyExpr);
          }
          goto after_match22;
        }
      }
      {
        if (_source75.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1582_boundName = _source75.dtor_boundName;
          DAST._IType _1583_boundType = _source75.dtor_boundType;
          DAST._IExpression _1584_overExpr = _source75.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1585_body = _source75.dtor_body;
          {
            RAST._IExpr _1586_over;
            DCOMP._IOwnership _1587___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1588_recIdents;
            RAST._IExpr _out160;
            DCOMP._IOwnership _out161;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out162;
            (this).GenExpr(_1584_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out160, out _out161, out _out162);
            _1586_over = _out160;
            _1587___v85 = _out161;
            _1588_recIdents = _out162;
            if (((_1584_overExpr).is_MapBoundedPool) || ((_1584_overExpr).is_SetBoundedPool)) {
              _1586_over = ((_1586_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1589_boundTpe;
            RAST._IType _out163;
            _out163 = (this).GenType(_1583_boundType, DCOMP.GenTypeContext.@default());
            _1589_boundTpe = _out163;
            readIdents = _1588_recIdents;
            Dafny.ISequence<Dafny.Rune> _1590_boundRName;
            _1590_boundRName = DCOMP.__default.escapeName(_1582_boundName);
            RAST._IExpr _1591_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1592_bodyIdents;
            DCOMP._IEnvironment _1593_bodyEnv;
            RAST._IExpr _out164;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out165;
            DCOMP._IEnvironment _out166;
            (this).GenStmts(_1585_body, selfIdent, (env).AddAssigned(_1590_boundRName, _1589_boundTpe), false, earlyReturn, out _out164, out _out165, out _out166);
            _1591_bodyExpr = _out164;
            _1592_bodyIdents = _out165;
            _1593_bodyEnv = _out166;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1592_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1590_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1590_boundRName, _1586_over, _1591_bodyExpr);
          }
          goto after_match22;
        }
      }
      {
        if (_source75.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1594_toLabel = _source75.dtor_toLabel;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source76 = _1594_toLabel;
            {
              if (_source76.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1595_lbl = _source76.dtor_value;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1595_lbl)));
                }
                goto after_match23;
              }
            }
            {
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
          after_match23: ;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match22;
        }
      }
      {
        if (_source75.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1596_body = _source75.dtor_body;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _1597_selfClone;
              DCOMP._IOwnership _1598___v86;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1599___v87;
              RAST._IExpr _out167;
              DCOMP._IOwnership _out168;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out169;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out167, out _out168, out _out169);
              _1597_selfClone = _out167;
              _1598___v86 = _out168;
              _1599___v87 = _out169;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1597_selfClone)));
            }
            newEnv = env;
            BigInteger _hi35 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1600_paramI = BigInteger.Zero; _1600_paramI < _hi35; _1600_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1601_param;
              _1601_param = ((env).dtor_names).Select(_1600_paramI);
              RAST._IExpr _1602_paramInit;
              DCOMP._IOwnership _1603___v88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1604___v89;
              RAST._IExpr _out170;
              DCOMP._IOwnership _out171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out172;
              (this).GenIdent(_1601_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out170, out _out171, out _out172);
              _1602_paramInit = _out170;
              _1603___v88 = _out171;
              _1604___v89 = _out172;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1601_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1602_paramInit)));
              if (((env).dtor_types).Contains(_1601_param)) {
                RAST._IType _1605_declaredType;
                _1605_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1601_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1601_param, _1605_declaredType);
              }
            }
            RAST._IExpr _1606_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1607_bodyIdents;
            DCOMP._IEnvironment _1608_bodyEnv;
            RAST._IExpr _out173;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out174;
            DCOMP._IEnvironment _out175;
            (this).GenStmts(_1596_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out173, out _out174, out _out175);
            _1606_bodyExpr = _out173;
            _1607_bodyIdents = _out174;
            _1608_bodyEnv = _out175;
            readIdents = _1607_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1606_bodyExpr)));
          }
          goto after_match22;
        }
      }
      {
        if (_source75.is_JumpTailCallStart) {
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match22;
        }
      }
      {
        if (_source75.is_Call) {
          DAST._IExpression _1609_on = _source75.dtor_on;
          DAST._ICallName _1610_name = _source75.dtor_callName;
          Dafny.ISequence<DAST._IType> _1611_typeArgs = _source75.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1612_args = _source75.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1613_maybeOutVars = _source75.dtor_outs;
          {
            Dafny.ISequence<RAST._IExpr> _1614_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1615_recIdents;
            Dafny.ISequence<RAST._IType> _1616_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _1617_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out176;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
            Dafny.ISequence<RAST._IType> _out178;
            Std.Wrappers._IOption<DAST._IResolvedType> _out179;
            (this).GenArgs(selfIdent, _1610_name, _1611_typeArgs, _1612_args, env, out _out176, out _out177, out _out178, out _out179);
            _1614_argExprs = _out176;
            _1615_recIdents = _out177;
            _1616_typeExprs = _out178;
            _1617_fullNameQualifier = _out179;
            readIdents = _1615_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source77 = _1617_fullNameQualifier;
            {
              if (_source77.is_Some) {
                DAST._IResolvedType value9 = _source77.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1618_path = value9.dtor_path;
                Dafny.ISequence<DAST._IType> _1619_onTypeArgs = value9.dtor_typeArgs;
                DAST._IResolvedTypeBase _1620_base = value9.dtor_kind;
                RAST._IExpr _1621_fullPath;
                RAST._IExpr _out180;
                _out180 = DCOMP.COMP.GenPathExpr(_1618_path);
                _1621_fullPath = _out180;
                Dafny.ISequence<RAST._IType> _1622_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out181;
                _out181 = (this).GenTypeArgs(_1619_onTypeArgs, DCOMP.GenTypeContext.@default());
                _1622_onTypeExprs = _out181;
                RAST._IExpr _1623_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _1624_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1625_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1620_base).is_Trait) || ((_1620_base).is_Class)) {
                  RAST._IExpr _out182;
                  DCOMP._IOwnership _out183;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out184;
                  (this).GenExpr(_1609_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out182, out _out183, out _out184);
                  _1623_onExpr = _out182;
                  _1624_recOwnership = _out183;
                  _1625_recIdents = _out184;
                  _1623_onExpr = ((this).modify__macro).Apply1(_1623_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1625_recIdents);
                } else {
                  RAST._IExpr _out185;
                  DCOMP._IOwnership _out186;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out187;
                  (this).GenExpr(_1609_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out185, out _out186, out _out187);
                  _1623_onExpr = _out185;
                  _1624_recOwnership = _out186;
                  _1625_recIdents = _out187;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1625_recIdents);
                }
                generated = ((((_1621_fullPath).ApplyType(_1622_onTypeExprs)).MSel(DCOMP.__default.escapeName((_1610_name).dtor_name))).ApplyType(_1616_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_1623_onExpr), _1614_argExprs));
                goto after_match24;
              }
            }
            {
              RAST._IExpr _1626_onExpr;
              DCOMP._IOwnership _1627___v94;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1628_enclosingIdents;
              RAST._IExpr _out188;
              DCOMP._IOwnership _out189;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out190;
              (this).GenExpr(_1609_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out188, out _out189, out _out190);
              _1626_onExpr = _out188;
              _1627___v94 = _out189;
              _1628_enclosingIdents = _out190;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1628_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _1629_renderedName;
              DAST._ICallName _source78 = _1610_name;
              {
                if (_source78.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _1630_name = _source78.dtor_name;
                  _1629_renderedName = DCOMP.__default.escapeName(_1630_name);
                  goto after_match25;
                }
              }
              {
                bool disjunctiveMatch11 = false;
                if (_source78.is_MapBuilderAdd) {
                  disjunctiveMatch11 = true;
                }
                if (_source78.is_SetBuilderAdd) {
                  disjunctiveMatch11 = true;
                }
                if (disjunctiveMatch11) {
                  _1629_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                  goto after_match25;
                }
              }
              {
                _1629_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
              }
            after_match25: ;
              DAST._IExpression _source79 = _1609_on;
              {
                if (_source79.is_Companion) {
                  {
                    _1626_onExpr = (_1626_onExpr).MSel(_1629_renderedName);
                  }
                  goto after_match26;
                }
              }
              {
                {
                  if (!object.Equals(_1626_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source80 = _1610_name;
                    {
                      if (_source80.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source80.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _1631_tpe = onType0.dtor_value;
                          RAST._IType _1632_typ;
                          RAST._IType _out191;
                          _out191 = (this).GenType(_1631_tpe, DCOMP.GenTypeContext.@default());
                          _1632_typ = _out191;
                          if (((_1632_typ).IsObjectOrPointer()) && (!object.Equals(_1626_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _1626_onExpr = ((this).modify__macro).Apply1(_1626_onExpr);
                          }
                          goto after_match27;
                        }
                      }
                    }
                    {
                    }
                  after_match27: ;
                  }
                  _1626_onExpr = (_1626_onExpr).Sel(_1629_renderedName);
                }
              }
            after_match26: ;
              generated = ((_1626_onExpr).ApplyType(_1616_typeExprs)).Apply(_1614_argExprs);
            }
          after_match24: ;
            if (((_1613_maybeOutVars).is_Some) && ((new BigInteger(((_1613_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1633_outVar;
              _1633_outVar = DCOMP.__default.escapeName((((_1613_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
              if (!((env).CanReadWithoutClone(_1633_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1633_outVar, generated);
            } else if (((_1613_maybeOutVars).is_None) || ((new BigInteger(((_1613_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1634_tmpVar;
              _1634_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1635_tmpId;
              _1635_tmpId = RAST.Expr.create_Identifier(_1634_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1634_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1636_outVars;
              _1636_outVars = (_1613_maybeOutVars).dtor_value;
              BigInteger _hi36 = new BigInteger((_1636_outVars).Count);
              for (BigInteger _1637_outI = BigInteger.Zero; _1637_outI < _hi36; _1637_outI++) {
                Dafny.ISequence<Dafny.Rune> _1638_outVar;
                _1638_outVar = DCOMP.__default.escapeName(((_1636_outVars).Select(_1637_outI)));
                RAST._IExpr _1639_rhs;
                _1639_rhs = (_1635_tmpId).Sel(Std.Strings.__default.OfNat(_1637_outI));
                if (!((env).CanReadWithoutClone(_1638_outVar))) {
                  _1639_rhs = RAST.__default.MaybePlacebo(_1639_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1638_outVar, _1639_rhs));
              }
            }
            newEnv = env;
          }
          goto after_match22;
        }
      }
      {
        if (_source75.is_Return) {
          DAST._IExpression _1640_exprDafny = _source75.dtor_expr;
          {
            RAST._IExpr _1641_expr;
            DCOMP._IOwnership _1642___v105;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1643_recIdents;
            RAST._IExpr _out192;
            DCOMP._IOwnership _out193;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out194;
            (this).GenExpr(_1640_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out192, out _out193, out _out194);
            _1641_expr = _out192;
            _1642___v105 = _out193;
            _1643_recIdents = _out194;
            readIdents = _1643_recIdents;
            if (isLast) {
              generated = _1641_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1641_expr));
            }
            newEnv = env;
          }
          goto after_match22;
        }
      }
      {
        if (_source75.is_EarlyReturn) {
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source81 = earlyReturn;
            {
              if (_source81.is_None) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
                goto after_match28;
              }
            }
            {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1644_rustIdents = _source81.dtor_value;
              Dafny.ISequence<RAST._IExpr> _1645_tupleArgs;
              _1645_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi37 = new BigInteger((_1644_rustIdents).Count);
              for (BigInteger _1646_i = BigInteger.Zero; _1646_i < _hi37; _1646_i++) {
                RAST._IExpr _1647_rIdent;
                DCOMP._IOwnership _1648___v106;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1649___v107;
                RAST._IExpr _out195;
                DCOMP._IOwnership _out196;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out197;
                (this).GenIdent((_1644_rustIdents).Select(_1646_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out195, out _out196, out _out197);
                _1647_rIdent = _out195;
                _1648___v106 = _out196;
                _1649___v107 = _out197;
                _1645_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1645_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1647_rIdent));
              }
              if ((new BigInteger((_1645_tupleArgs).Count)) == (BigInteger.One)) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1645_tupleArgs).Select(BigInteger.Zero)));
              } else {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1645_tupleArgs)));
              }
            }
          after_match28: ;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match22;
        }
      }
      {
        if (_source75.is_Halt) {
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match22;
        }
      }
      {
        DAST._IExpression _1650_e = _source75.dtor_Print_a0;
        {
          RAST._IExpr _1651_printedExpr;
          DCOMP._IOwnership _1652_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1653_recIdents;
          RAST._IExpr _out198;
          DCOMP._IOwnership _out199;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out200;
          (this).GenExpr(_1650_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out198, out _out199, out _out200);
          _1651_printedExpr = _out198;
          _1652_recOwnership = _out199;
          _1653_recIdents = _out200;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1651_printedExpr)));
          readIdents = _1653_recIdents;
          newEnv = env;
        }
      }
    after_match22: ;
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source82 = range;
      {
        if (_source82.is_NoRange) {
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      {
        if (_source82.is_U8) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      {
        if (_source82.is_U16) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      {
        if (_source82.is_U32) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      {
        if (_source82.is_U64) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      {
        if (_source82.is_U128) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      {
        if (_source82.is_I8) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      {
        if (_source82.is_I16) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      {
        if (_source82.is_I32) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      {
        if (_source82.is_I64) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      {
        if (_source82.is_I128) {
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
      DAST._IExpression _source83 = e;
      {
        if (_source83.is_Literal) {
          DAST._ILiteral _h170 = _source83.dtor_Literal_a0;
          if (_h170.is_BoolLiteral) {
            bool _1654_b = _h170.dtor_BoolLiteral_a0;
            {
              RAST._IExpr _out205;
              DCOMP._IOwnership _out206;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_1654_b), expectedOwnership, out _out205, out _out206);
              r = _out205;
              resultingOwnership = _out206;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match29;
          }
        }
      }
      {
        if (_source83.is_Literal) {
          DAST._ILiteral _h171 = _source83.dtor_Literal_a0;
          if (_h171.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1655_i = _h171.dtor_IntLiteral_a0;
            DAST._IType _1656_t = _h171.dtor_IntLiteral_a1;
            {
              DAST._IType _source84 = _1656_t;
              {
                if (_source84.is_Primitive) {
                  DAST._IPrimitive _h70 = _source84.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    {
                      if ((new BigInteger((_1655_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1655_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1655_i, true, false));
                      }
                    }
                    goto after_match30;
                  }
                }
              }
              {
                DAST._IType _1657_o = _source84;
                {
                  RAST._IType _1658_genType;
                  RAST._IType _out207;
                  _out207 = (this).GenType(_1657_o, DCOMP.GenTypeContext.@default());
                  _1658_genType = _out207;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1655_i), _1658_genType);
                }
              }
            after_match30: ;
              RAST._IExpr _out208;
              DCOMP._IOwnership _out209;
              (this).FromOwned(r, expectedOwnership, out _out208, out _out209);
              r = _out208;
              resultingOwnership = _out209;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match29;
          }
        }
      }
      {
        if (_source83.is_Literal) {
          DAST._ILiteral _h172 = _source83.dtor_Literal_a0;
          if (_h172.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1659_n = _h172.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1660_d = _h172.dtor_DecLiteral_a1;
            DAST._IType _1661_t = _h172.dtor_DecLiteral_a2;
            {
              DAST._IType _source85 = _1661_t;
              {
                if (_source85.is_Primitive) {
                  DAST._IPrimitive _h71 = _source85.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1659_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1660_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                    goto after_match31;
                  }
                }
              }
              {
                DAST._IType _1662_o = _source85;
                {
                  RAST._IType _1663_genType;
                  RAST._IType _out210;
                  _out210 = (this).GenType(_1662_o, DCOMP.GenTypeContext.@default());
                  _1663_genType = _out210;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1659_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1660_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1663_genType);
                }
              }
            after_match31: ;
              RAST._IExpr _out211;
              DCOMP._IOwnership _out212;
              (this).FromOwned(r, expectedOwnership, out _out211, out _out212);
              r = _out211;
              resultingOwnership = _out212;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match29;
          }
        }
      }
      {
        if (_source83.is_Literal) {
          DAST._ILiteral _h173 = _source83.dtor_Literal_a0;
          if (_h173.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1664_l = _h173.dtor_StringLiteral_a0;
            bool _1665_verbatim = _h173.dtor_verbatim;
            {
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1664_l, false, _1665_verbatim));
              RAST._IExpr _out213;
              DCOMP._IOwnership _out214;
              (this).FromOwned(r, expectedOwnership, out _out213, out _out214);
              r = _out213;
              resultingOwnership = _out214;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match29;
          }
        }
      }
      {
        if (_source83.is_Literal) {
          DAST._ILiteral _h174 = _source83.dtor_Literal_a0;
          if (_h174.is_CharLiteralUTF16) {
            BigInteger _1666_c = _h174.dtor_CharLiteralUTF16_a0;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1666_c));
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
            goto after_match29;
          }
        }
      }
      {
        if (_source83.is_Literal) {
          DAST._ILiteral _h175 = _source83.dtor_Literal_a0;
          if (_h175.is_CharLiteral) {
            Dafny.Rune _1667_c = _h175.dtor_CharLiteral_a0;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1667_c).Value)));
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
            goto after_match29;
          }
        }
      }
      {
        DAST._ILiteral _h176 = _source83.dtor_Literal_a0;
        DAST._IType _1668_tpe = _h176.dtor_Null_a0;
        {
          RAST._IType _1669_tpeGen;
          RAST._IType _out219;
          _out219 = (this).GenType(_1668_tpe, DCOMP.GenTypeContext.@default());
          _1669_tpeGen = _out219;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null"));
          } else {
            r = RAST.Expr.create_TypeAscription(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _1669_tpeGen);
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
    after_match29: ;
    }
    public void GenExprBinary(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IBinOp _1670_op = _let_tmp_rhs54.dtor_op;
      DAST._IExpression _1671_lExpr = _let_tmp_rhs54.dtor_left;
      DAST._IExpression _1672_rExpr = _let_tmp_rhs54.dtor_right;
      DAST.Format._IBinaryOpFormat _1673_format = _let_tmp_rhs54.dtor_format2;
      bool _1674_becomesLeftCallsRight;
      DAST._IBinOp _source86 = _1670_op;
      {
        bool disjunctiveMatch12 = false;
        if (_source86.is_SetMerge) {
          disjunctiveMatch12 = true;
        }
        if (_source86.is_SetSubtraction) {
          disjunctiveMatch12 = true;
        }
        if (_source86.is_SetIntersection) {
          disjunctiveMatch12 = true;
        }
        if (_source86.is_SetDisjoint) {
          disjunctiveMatch12 = true;
        }
        if (_source86.is_MapMerge) {
          disjunctiveMatch12 = true;
        }
        if (_source86.is_MapSubtraction) {
          disjunctiveMatch12 = true;
        }
        if (_source86.is_MultisetMerge) {
          disjunctiveMatch12 = true;
        }
        if (_source86.is_MultisetSubtraction) {
          disjunctiveMatch12 = true;
        }
        if (_source86.is_MultisetIntersection) {
          disjunctiveMatch12 = true;
        }
        if (_source86.is_MultisetDisjoint) {
          disjunctiveMatch12 = true;
        }
        if (_source86.is_Concat) {
          disjunctiveMatch12 = true;
        }
        if (disjunctiveMatch12) {
          _1674_becomesLeftCallsRight = true;
          goto after_match32;
        }
      }
      {
        _1674_becomesLeftCallsRight = false;
      }
    after_match32: ;
      bool _1675_becomesRightCallsLeft;
      DAST._IBinOp _source87 = _1670_op;
      {
        if (_source87.is_In) {
          _1675_becomesRightCallsLeft = true;
          goto after_match33;
        }
      }
      {
        _1675_becomesRightCallsLeft = false;
      }
    after_match33: ;
      bool _1676_becomesCallLeftRight;
      DAST._IBinOp _source88 = _1670_op;
      {
        if (_source88.is_Eq) {
          bool referential0 = _source88.dtor_referential;
          if ((referential0) == (true)) {
            _1676_becomesCallLeftRight = false;
            goto after_match34;
          }
        }
      }
      {
        if (_source88.is_SetMerge) {
          _1676_becomesCallLeftRight = true;
          goto after_match34;
        }
      }
      {
        if (_source88.is_SetSubtraction) {
          _1676_becomesCallLeftRight = true;
          goto after_match34;
        }
      }
      {
        if (_source88.is_SetIntersection) {
          _1676_becomesCallLeftRight = true;
          goto after_match34;
        }
      }
      {
        if (_source88.is_SetDisjoint) {
          _1676_becomesCallLeftRight = true;
          goto after_match34;
        }
      }
      {
        if (_source88.is_MapMerge) {
          _1676_becomesCallLeftRight = true;
          goto after_match34;
        }
      }
      {
        if (_source88.is_MapSubtraction) {
          _1676_becomesCallLeftRight = true;
          goto after_match34;
        }
      }
      {
        if (_source88.is_MultisetMerge) {
          _1676_becomesCallLeftRight = true;
          goto after_match34;
        }
      }
      {
        if (_source88.is_MultisetSubtraction) {
          _1676_becomesCallLeftRight = true;
          goto after_match34;
        }
      }
      {
        if (_source88.is_MultisetIntersection) {
          _1676_becomesCallLeftRight = true;
          goto after_match34;
        }
      }
      {
        if (_source88.is_MultisetDisjoint) {
          _1676_becomesCallLeftRight = true;
          goto after_match34;
        }
      }
      {
        if (_source88.is_Concat) {
          _1676_becomesCallLeftRight = true;
          goto after_match34;
        }
      }
      {
        _1676_becomesCallLeftRight = false;
      }
    after_match34: ;
      DCOMP._IOwnership _1677_expectedLeftOwnership;
      if (_1674_becomesLeftCallsRight) {
        _1677_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipAutoBorrowed();
      } else if ((_1675_becomesRightCallsLeft) || (_1676_becomesCallLeftRight)) {
        _1677_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        _1677_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipOwned();
      }
      DCOMP._IOwnership _1678_expectedRightOwnership;
      if ((_1674_becomesLeftCallsRight) || (_1676_becomesCallLeftRight)) {
        _1678_expectedRightOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else if (_1675_becomesRightCallsLeft) {
        _1678_expectedRightOwnership = DCOMP.Ownership.create_OwnershipAutoBorrowed();
      } else {
        _1678_expectedRightOwnership = DCOMP.Ownership.create_OwnershipOwned();
      }
      RAST._IExpr _1679_left;
      DCOMP._IOwnership _1680___v112;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1681_recIdentsL;
      RAST._IExpr _out222;
      DCOMP._IOwnership _out223;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out224;
      (this).GenExpr(_1671_lExpr, selfIdent, env, _1677_expectedLeftOwnership, out _out222, out _out223, out _out224);
      _1679_left = _out222;
      _1680___v112 = _out223;
      _1681_recIdentsL = _out224;
      RAST._IExpr _1682_right;
      DCOMP._IOwnership _1683___v113;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1684_recIdentsR;
      RAST._IExpr _out225;
      DCOMP._IOwnership _out226;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out227;
      (this).GenExpr(_1672_rExpr, selfIdent, env, _1678_expectedRightOwnership, out _out225, out _out226, out _out227);
      _1682_right = _out225;
      _1683___v113 = _out226;
      _1684_recIdentsR = _out227;
      DAST._IBinOp _source89 = _1670_op;
      {
        if (_source89.is_In) {
          {
            r = ((_1682_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1679_left);
          }
          goto after_match35;
        }
      }
      {
        if (_source89.is_SeqProperPrefix) {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1679_left, _1682_right, _1673_format);
          goto after_match35;
        }
      }
      {
        if (_source89.is_SeqPrefix) {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1679_left, _1682_right, _1673_format);
          goto after_match35;
        }
      }
      {
        if (_source89.is_SetMerge) {
          {
            r = ((_1679_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1682_right);
          }
          goto after_match35;
        }
      }
      {
        if (_source89.is_SetSubtraction) {
          {
            r = ((_1679_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1682_right);
          }
          goto after_match35;
        }
      }
      {
        if (_source89.is_SetIntersection) {
          {
            r = ((_1679_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1682_right);
          }
          goto after_match35;
        }
      }
      {
        if (_source89.is_Subset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1679_left, _1682_right, _1673_format);
          }
          goto after_match35;
        }
      }
      {
        if (_source89.is_ProperSubset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1679_left, _1682_right, _1673_format);
          }
          goto after_match35;
        }
      }
      {
        if (_source89.is_SetDisjoint) {
          {
            r = ((_1679_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1682_right);
          }
          goto after_match35;
        }
      }
      {
        if (_source89.is_MapMerge) {
          {
            r = ((_1679_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1682_right);
          }
          goto after_match35;
        }
      }
      {
        if (_source89.is_MapSubtraction) {
          {
            r = ((_1679_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1682_right);
          }
          goto after_match35;
        }
      }
      {
        if (_source89.is_MultisetMerge) {
          {
            r = ((_1679_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1682_right);
          }
          goto after_match35;
        }
      }
      {
        if (_source89.is_MultisetSubtraction) {
          {
            r = ((_1679_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1682_right);
          }
          goto after_match35;
        }
      }
      {
        if (_source89.is_MultisetIntersection) {
          {
            r = ((_1679_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1682_right);
          }
          goto after_match35;
        }
      }
      {
        if (_source89.is_Submultiset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1679_left, _1682_right, _1673_format);
          }
          goto after_match35;
        }
      }
      {
        if (_source89.is_ProperSubmultiset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1679_left, _1682_right, _1673_format);
          }
          goto after_match35;
        }
      }
      {
        if (_source89.is_MultisetDisjoint) {
          {
            r = ((_1679_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1682_right);
          }
          goto after_match35;
        }
      }
      {
        if (_source89.is_Concat) {
          {
            r = ((_1679_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1682_right);
          }
          goto after_match35;
        }
      }
      {
        {
          if ((DCOMP.COMP.OpTable).Contains(_1670_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1670_op), _1679_left, _1682_right, _1673_format);
          } else {
            DAST._IBinOp _source90 = _1670_op;
            {
              if (_source90.is_Eq) {
                bool _1685_referential = _source90.dtor_referential;
                {
                  if (_1685_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1679_left, _1682_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_1672_rExpr).is_SeqValue) && ((new BigInteger(((_1672_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1679_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1671_lExpr).is_SeqValue) && ((new BigInteger(((_1671_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1682_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1679_left, _1682_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
                goto after_match36;
              }
            }
            {
              if (_source90.is_EuclidianDiv) {
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1679_left, _1682_right));
                }
                goto after_match36;
              }
            }
            {
              if (_source90.is_EuclidianMod) {
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1679_left, _1682_right));
                }
                goto after_match36;
              }
            }
            {
              Dafny.ISequence<Dafny.Rune> _1686_op = _source90.dtor_Passthrough_a0;
              {
                r = RAST.Expr.create_BinaryOp(_1686_op, _1679_left, _1682_right, _1673_format);
              }
            }
          after_match36: ;
          }
        }
      }
    after_match35: ;
      RAST._IExpr _out228;
      DCOMP._IOwnership _out229;
      (this).FromOwned(r, expectedOwnership, out _out228, out _out229);
      r = _out228;
      resultingOwnership = _out229;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1681_recIdentsL, _1684_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _1687_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _1688_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _1689_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _1689_toTpe;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1690_path = _let_tmp_rhs57.dtor_path;
      Dafny.ISequence<DAST._IType> _1691_typeArgs = _let_tmp_rhs57.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs58 = _let_tmp_rhs57.dtor_kind;
      DAST._IType _1692_b = _let_tmp_rhs58.dtor_baseType;
      DAST._INewtypeRange _1693_range = _let_tmp_rhs58.dtor_range;
      bool _1694_erase = _let_tmp_rhs58.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1695___v115 = _let_tmp_rhs57.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1696___v116 = _let_tmp_rhs57.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1697___v117 = _let_tmp_rhs57.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1698_nativeToType;
      _1698_nativeToType = DCOMP.COMP.NewtypeToRustType(_1692_b, _1693_range);
      if (object.Equals(_1688_fromTpe, _1692_b)) {
        RAST._IExpr _1699_recursiveGen;
        DCOMP._IOwnership _1700_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1701_recIdents;
        RAST._IExpr _out230;
        DCOMP._IOwnership _out231;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out232;
        (this).GenExpr(_1687_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out230, out _out231, out _out232);
        _1699_recursiveGen = _out230;
        _1700_recOwned = _out231;
        _1701_recIdents = _out232;
        readIdents = _1701_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source91 = _1698_nativeToType;
        {
          if (_source91.is_Some) {
            RAST._IType _1702_v = _source91.dtor_value;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1699_recursiveGen, RAST.Expr.create_ExprFromType(_1702_v)));
            RAST._IExpr _out233;
            DCOMP._IOwnership _out234;
            (this).FromOwned(r, expectedOwnership, out _out233, out _out234);
            r = _out233;
            resultingOwnership = _out234;
            goto after_match37;
          }
        }
        {
          if (_1694_erase) {
            r = _1699_recursiveGen;
          } else {
            RAST._IType _1703_rhsType;
            RAST._IType _out235;
            _out235 = (this).GenType(_1689_toTpe, DCOMP.GenTypeContext.InBinding());
            _1703_rhsType = _out235;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1703_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1699_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out236;
          DCOMP._IOwnership _out237;
          (this).FromOwnership(r, _1700_recOwned, expectedOwnership, out _out236, out _out237);
          r = _out236;
          resultingOwnership = _out237;
        }
      after_match37: ;
      } else {
        if ((_1698_nativeToType).is_Some) {
          DAST._IType _source92 = _1688_fromTpe;
          {
            if (_source92.is_UserDefined) {
              DAST._IResolvedType resolved1 = _source92.dtor_resolved;
              DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
              if (kind1.is_Newtype) {
                DAST._IType _1704_b0 = kind1.dtor_baseType;
                DAST._INewtypeRange _1705_range0 = kind1.dtor_range;
                bool _1706_erase0 = kind1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1707_attributes0 = resolved1.dtor_attributes;
                {
                  Std.Wrappers._IOption<RAST._IType> _1708_nativeFromType;
                  _1708_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1704_b0, _1705_range0);
                  if ((_1708_nativeFromType).is_Some) {
                    RAST._IExpr _1709_recursiveGen;
                    DCOMP._IOwnership _1710_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1711_recIdents;
                    RAST._IExpr _out238;
                    DCOMP._IOwnership _out239;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out240;
                    (this).GenExpr(_1687_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out238, out _out239, out _out240);
                    _1709_recursiveGen = _out238;
                    _1710_recOwned = _out239;
                    _1711_recIdents = _out240;
                    RAST._IExpr _out241;
                    DCOMP._IOwnership _out242;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_1709_recursiveGen, (_1698_nativeToType).dtor_value), _1710_recOwned, expectedOwnership, out _out241, out _out242);
                    r = _out241;
                    resultingOwnership = _out242;
                    readIdents = _1711_recIdents;
                    return ;
                  }
                }
                goto after_match38;
              }
            }
          }
          {
          }
        after_match38: ;
          if (object.Equals(_1688_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1712_recursiveGen;
            DCOMP._IOwnership _1713_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1714_recIdents;
            RAST._IExpr _out243;
            DCOMP._IOwnership _out244;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out245;
            (this).GenExpr(_1687_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out243, out _out244, out _out245);
            _1712_recursiveGen = _out243;
            _1713_recOwned = _out244;
            _1714_recIdents = _out245;
            RAST._IExpr _out246;
            DCOMP._IOwnership _out247;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_1712_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1698_nativeToType).dtor_value), _1713_recOwned, expectedOwnership, out _out246, out _out247);
            r = _out246;
            resultingOwnership = _out247;
            readIdents = _1714_recIdents;
            return ;
          }
        }
        RAST._IExpr _out248;
        DCOMP._IOwnership _out249;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out250;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1687_expr, _1688_fromTpe, _1692_b), _1692_b, _1689_toTpe), selfIdent, env, expectedOwnership, out _out248, out _out249, out _out250);
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
      DAST._IExpression _1715_expr = _let_tmp_rhs59.dtor_value;
      DAST._IType _1716_fromTpe = _let_tmp_rhs59.dtor_from;
      DAST._IType _1717_toTpe = _let_tmp_rhs59.dtor_typ;
      DAST._IType _let_tmp_rhs60 = _1716_fromTpe;
      DAST._IResolvedType _let_tmp_rhs61 = _let_tmp_rhs60.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1718___v123 = _let_tmp_rhs61.dtor_path;
      Dafny.ISequence<DAST._IType> _1719___v124 = _let_tmp_rhs61.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs62 = _let_tmp_rhs61.dtor_kind;
      DAST._IType _1720_b = _let_tmp_rhs62.dtor_baseType;
      DAST._INewtypeRange _1721_range = _let_tmp_rhs62.dtor_range;
      bool _1722_erase = _let_tmp_rhs62.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1723_attributes = _let_tmp_rhs61.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1724___v125 = _let_tmp_rhs61.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1725___v126 = _let_tmp_rhs61.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1726_nativeFromType;
      _1726_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1720_b, _1721_range);
      if (object.Equals(_1720_b, _1717_toTpe)) {
        RAST._IExpr _1727_recursiveGen;
        DCOMP._IOwnership _1728_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1729_recIdents;
        RAST._IExpr _out251;
        DCOMP._IOwnership _out252;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out253;
        (this).GenExpr(_1715_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out251, out _out252, out _out253);
        _1727_recursiveGen = _out251;
        _1728_recOwned = _out252;
        _1729_recIdents = _out253;
        readIdents = _1729_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source93 = _1726_nativeFromType;
        {
          if (_source93.is_Some) {
            RAST._IType _1730_v = _source93.dtor_value;
            RAST._IType _1731_toTpeRust;
            RAST._IType _out254;
            _out254 = (this).GenType(_1717_toTpe, DCOMP.GenTypeContext.@default());
            _1731_toTpeRust = _out254;
            r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1731_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1727_recursiveGen));
            RAST._IExpr _out255;
            DCOMP._IOwnership _out256;
            (this).FromOwned(r, expectedOwnership, out _out255, out _out256);
            r = _out255;
            resultingOwnership = _out256;
            goto after_match39;
          }
        }
        {
          if (_1722_erase) {
            r = _1727_recursiveGen;
          } else {
            r = (_1727_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out257;
          DCOMP._IOwnership _out258;
          (this).FromOwnership(r, _1728_recOwned, expectedOwnership, out _out257, out _out258);
          r = _out257;
          resultingOwnership = _out258;
        }
      after_match39: ;
      } else {
        if ((_1726_nativeFromType).is_Some) {
          if (object.Equals(_1717_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1732_recursiveGen;
            DCOMP._IOwnership _1733_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1734_recIdents;
            RAST._IExpr _out259;
            DCOMP._IOwnership _out260;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out261;
            (this).GenExpr(_1715_expr, selfIdent, env, expectedOwnership, out _out259, out _out260, out _out261);
            _1732_recursiveGen = _out259;
            _1733_recOwned = _out260;
            _1734_recIdents = _out261;
            RAST._IExpr _out262;
            DCOMP._IOwnership _out263;
            (this).FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1732_recursiveGen, (this).DafnyCharUnderlying)), _1733_recOwned, expectedOwnership, out _out262, out _out263);
            r = _out262;
            resultingOwnership = _out263;
            readIdents = _1734_recIdents;
            return ;
          }
        }
        RAST._IExpr _out264;
        DCOMP._IOwnership _out265;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out266;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1715_expr, _1716_fromTpe, _1720_b), _1720_b, _1717_toTpe), selfIdent, env, expectedOwnership, out _out264, out _out265, out _out266);
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
        Std.Wrappers._IResult<__T, __E> _1735_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_1735_valueOrError0).IsFailure()) {
          return (_1735_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1736_head = (_1735_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _1737_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_1737_valueOrError1).IsFailure()) {
            return (_1737_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _1738_tail = (_1737_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1736_head), _1738_tail));
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
          RAST._IType _1739_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          RAST._IType _1740_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel((this).upcast)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1739_fromTpeUnderlying, _1740_toTpeUnderlying))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1741_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_1741_valueOrError0).IsFailure()) {
          return (_1741_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1742_lambda = (_1741_valueOrError0).Extract();
          if ((fromType).is_Arrow) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(_1742_lambda);
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).Apply1(_1742_lambda));
          }
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1743_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim12 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr12 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
          for (int i12 = 0; i12 < dim12; i12++) {
            var _1744_i = (BigInteger) i12;
            arr12[(int)(_1744_i)] = (this).UpcastConversionLambda((((fromType).dtor_resolved).dtor_typeArgs).Select(_1744_i), ((fromTpe).dtor_arguments).Select(_1744_i), (((toType).dtor_resolved).dtor_typeArgs).Select(_1744_i), ((toTpe).dtor_arguments).Select(_1744_i), typeParams);
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr12);
        }))());
        if ((_1743_valueOrError1).IsFailure()) {
          return (_1743_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _1745_lambdas = (_1743_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim13 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr13 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim13, "array size exceeds memory limit")];
  for (int i13 = 0; i13 < dim13; i13++) {
    var _1746_i = (BigInteger) i13;
    arr13[(int)(_1746_i)] = ((fromTpe).dtor_arguments).Select(_1746_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr13);
}))())).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_1745_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _1747_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _1748_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _1749_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _1750_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1751_valueOrError2 = (this).UpcastConversionLambda(_1749_newFromType, _1747_newFromTpe, _1750_newToType, _1748_newToTpe, typeParams);
        if ((_1751_valueOrError2).IsFailure()) {
          return (_1751_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1752_coerceArg = (_1751_valueOrError2).Extract();
          RAST._IExpr _1753_collectionType = (RAST.__default.dafny__runtime).MSel(((fromTpe).dtor_baseName).dtor_name);
          RAST._IExpr _1754_baseType = (((((fromTpe).dtor_baseName).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? ((_1753_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((fromTpe).dtor_arguments).Select(BigInteger.Zero), _1747_newFromTpe))) : ((_1753_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1747_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_1754_baseType).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_1752_coerceArg));
        }
      } else if ((((((((((fromTpe).is_DynType) && (((fromTpe).dtor_underlying).is_FnType)) && ((toTpe).is_DynType)) && (((toTpe).dtor_underlying).is_FnType)) && ((((fromTpe).dtor_underlying).dtor_arguments).Equals(((toTpe).dtor_underlying).dtor_arguments))) && ((fromType).is_Arrow)) && ((toType).is_Arrow)) && ((new BigInteger((((fromTpe).dtor_underlying).dtor_arguments).Count)) == (BigInteger.One))) && (((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).is_Borrowed)) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1755_valueOrError3 = (this).UpcastConversionLambda((fromType).dtor_result, ((fromTpe).dtor_underlying).dtor_returnType, (toType).dtor_result, ((toTpe).dtor_underlying).dtor_returnType, typeParams);
        if ((_1755_valueOrError3).IsFailure()) {
          return (_1755_valueOrError3).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1756_lambda = (_1755_valueOrError3).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn1_coerce"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying, ((fromTpe).dtor_underlying).dtor_returnType, ((toTpe).dtor_underlying).dtor_returnType))).Apply1(_1756_lambda));
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
      DAST._IExpression _1757_expr = _let_tmp_rhs63.dtor_value;
      DAST._IType _1758_fromTpe = _let_tmp_rhs63.dtor_from;
      DAST._IType _1759_toTpe = _let_tmp_rhs63.dtor_typ;
      RAST._IType _1760_fromTpeGen;
      RAST._IType _out267;
      _out267 = (this).GenType(_1758_fromTpe, DCOMP.GenTypeContext.InBinding());
      _1760_fromTpeGen = _out267;
      RAST._IType _1761_toTpeGen;
      RAST._IType _out268;
      _out268 = (this).GenType(_1759_toTpe, DCOMP.GenTypeContext.InBinding());
      _1761_toTpeGen = _out268;
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1762_upcastConverter;
      _1762_upcastConverter = (this).UpcastConversionLambda(_1758_fromTpe, _1760_fromTpeGen, _1759_toTpe, _1761_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_1762_upcastConverter).is_Success) {
        RAST._IExpr _1763_conversionLambda;
        _1763_conversionLambda = (_1762_upcastConverter).dtor_value;
        RAST._IExpr _1764_recursiveGen;
        DCOMP._IOwnership _1765_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1766_recIdents;
        RAST._IExpr _out269;
        DCOMP._IOwnership _out270;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out271;
        (this).GenExpr(_1757_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out269, out _out270, out _out271);
        _1764_recursiveGen = _out269;
        _1765_recOwned = _out270;
        _1766_recIdents = _out271;
        readIdents = _1766_recIdents;
        r = (_1763_conversionLambda).Apply1(_1764_recursiveGen);
        RAST._IExpr _out272;
        DCOMP._IOwnership _out273;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out272, out _out273);
        r = _out272;
        resultingOwnership = _out273;
      } else if ((this).IsDowncastConversion(_1760_fromTpeGen, _1761_toTpeGen)) {
        RAST._IExpr _1767_recursiveGen;
        DCOMP._IOwnership _1768_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1769_recIdents;
        RAST._IExpr _out274;
        DCOMP._IOwnership _out275;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out276;
        (this).GenExpr(_1757_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out274, out _out275, out _out276);
        _1767_recursiveGen = _out274;
        _1768_recOwned = _out275;
        _1769_recIdents = _out276;
        readIdents = _1769_recIdents;
        _1761_toTpeGen = (_1761_toTpeGen).ObjectOrPointerUnderlying();
        r = ((RAST.__default.dafny__runtime).MSel((this).downcast)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1767_recursiveGen, RAST.Expr.create_ExprFromType(_1761_toTpeGen)));
        RAST._IExpr _out277;
        DCOMP._IOwnership _out278;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out277, out _out278);
        r = _out277;
        resultingOwnership = _out278;
      } else {
        RAST._IExpr _1770_recursiveGen;
        DCOMP._IOwnership _1771_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1772_recIdents;
        RAST._IExpr _out279;
        DCOMP._IOwnership _out280;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out281;
        (this).GenExpr(_1757_expr, selfIdent, env, expectedOwnership, out _out279, out _out280, out _out281);
        _1770_recursiveGen = _out279;
        _1771_recOwned = _out280;
        _1772_recIdents = _out281;
        readIdents = _1772_recIdents;
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _let_tmp_rhs64 = _1762_upcastConverter;
        _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>> _let_tmp_rhs65 = _let_tmp_rhs64.dtor_error;
        DAST._IType _1773_fromType = _let_tmp_rhs65.dtor__0;
        RAST._IType _1774_fromTpeGen = _let_tmp_rhs65.dtor__1;
        DAST._IType _1775_toType = _let_tmp_rhs65.dtor__2;
        RAST._IType _1776_toTpeGen = _let_tmp_rhs65.dtor__3;
        Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1777_m = _let_tmp_rhs65.dtor__4;
        Dafny.ISequence<Dafny.Rune> _1778_msg;
        _1778_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1774_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1776_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1778_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1770_recursiveGen)._ToString(DCOMP.__default.IND), _1778_msg));
        RAST._IExpr _out282;
        DCOMP._IOwnership _out283;
        (this).FromOwnership(r, _1771_recOwned, expectedOwnership, out _out282, out _out283);
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
      DAST._IExpression _1779_expr = _let_tmp_rhs66.dtor_value;
      DAST._IType _1780_fromTpe = _let_tmp_rhs66.dtor_from;
      DAST._IType _1781_toTpe = _let_tmp_rhs66.dtor_typ;
      if (object.Equals(_1780_fromTpe, _1781_toTpe)) {
        RAST._IExpr _1782_recursiveGen;
        DCOMP._IOwnership _1783_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1784_recIdents;
        RAST._IExpr _out284;
        DCOMP._IOwnership _out285;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out286;
        (this).GenExpr(_1779_expr, selfIdent, env, expectedOwnership, out _out284, out _out285, out _out286);
        _1782_recursiveGen = _out284;
        _1783_recOwned = _out285;
        _1784_recIdents = _out286;
        r = _1782_recursiveGen;
        RAST._IExpr _out287;
        DCOMP._IOwnership _out288;
        (this).FromOwnership(r, _1783_recOwned, expectedOwnership, out _out287, out _out288);
        r = _out287;
        resultingOwnership = _out288;
        readIdents = _1784_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source94 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1780_fromTpe, _1781_toTpe);
        {
          DAST._IType _10 = _source94.dtor__1;
          if (_10.is_UserDefined) {
            DAST._IResolvedType resolved2 = _10.dtor_resolved;
            DAST._IResolvedTypeBase kind2 = resolved2.dtor_kind;
            if (kind2.is_Newtype) {
              DAST._IType _1785_b = kind2.dtor_baseType;
              DAST._INewtypeRange _1786_range = kind2.dtor_range;
              bool _1787_erase = kind2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1788_attributes = resolved2.dtor_attributes;
              {
                RAST._IExpr _out289;
                DCOMP._IOwnership _out290;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out291;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out289, out _out290, out _out291);
                r = _out289;
                resultingOwnership = _out290;
                readIdents = _out291;
              }
              goto after_match40;
            }
          }
        }
        {
          DAST._IType _00 = _source94.dtor__0;
          if (_00.is_UserDefined) {
            DAST._IResolvedType resolved3 = _00.dtor_resolved;
            DAST._IResolvedTypeBase kind3 = resolved3.dtor_kind;
            if (kind3.is_Newtype) {
              DAST._IType _1789_b = kind3.dtor_baseType;
              DAST._INewtypeRange _1790_range = kind3.dtor_range;
              bool _1791_erase = kind3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1792_attributes = resolved3.dtor_attributes;
              {
                RAST._IExpr _out292;
                DCOMP._IOwnership _out293;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out294;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out292, out _out293, out _out294);
                r = _out292;
                resultingOwnership = _out293;
                readIdents = _out294;
              }
              goto after_match40;
            }
          }
        }
        {
          DAST._IType _01 = _source94.dtor__0;
          if (_01.is_Primitive) {
            DAST._IPrimitive _h72 = _01.dtor_Primitive_a0;
            if (_h72.is_Int) {
              DAST._IType _11 = _source94.dtor__1;
              if (_11.is_Primitive) {
                DAST._IPrimitive _h73 = _11.dtor_Primitive_a0;
                if (_h73.is_Real) {
                  {
                    RAST._IExpr _1793_recursiveGen;
                    DCOMP._IOwnership _1794___v137;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1795_recIdents;
                    RAST._IExpr _out295;
                    DCOMP._IOwnership _out296;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out297;
                    (this).GenExpr(_1779_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out295, out _out296, out _out297);
                    _1793_recursiveGen = _out295;
                    _1794___v137 = _out296;
                    _1795_recIdents = _out297;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1793_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out298;
                    DCOMP._IOwnership _out299;
                    (this).FromOwned(r, expectedOwnership, out _out298, out _out299);
                    r = _out298;
                    resultingOwnership = _out299;
                    readIdents = _1795_recIdents;
                  }
                  goto after_match40;
                }
              }
            }
          }
        }
        {
          DAST._IType _02 = _source94.dtor__0;
          if (_02.is_Primitive) {
            DAST._IPrimitive _h74 = _02.dtor_Primitive_a0;
            if (_h74.is_Real) {
              DAST._IType _12 = _source94.dtor__1;
              if (_12.is_Primitive) {
                DAST._IPrimitive _h75 = _12.dtor_Primitive_a0;
                if (_h75.is_Int) {
                  {
                    RAST._IExpr _1796_recursiveGen;
                    DCOMP._IOwnership _1797___v138;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1798_recIdents;
                    RAST._IExpr _out300;
                    DCOMP._IOwnership _out301;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out302;
                    (this).GenExpr(_1779_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out300, out _out301, out _out302);
                    _1796_recursiveGen = _out300;
                    _1797___v138 = _out301;
                    _1798_recIdents = _out302;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1796_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out303;
                    DCOMP._IOwnership _out304;
                    (this).FromOwned(r, expectedOwnership, out _out303, out _out304);
                    r = _out303;
                    resultingOwnership = _out304;
                    readIdents = _1798_recIdents;
                  }
                  goto after_match40;
                }
              }
            }
          }
        }
        {
          DAST._IType _03 = _source94.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h76 = _03.dtor_Primitive_a0;
            if (_h76.is_Int) {
              DAST._IType _13 = _source94.dtor__1;
              if (_13.is_Passthrough) {
                {
                  RAST._IType _1799_rhsType;
                  RAST._IType _out305;
                  _out305 = (this).GenType(_1781_toTpe, DCOMP.GenTypeContext.InBinding());
                  _1799_rhsType = _out305;
                  RAST._IExpr _1800_recursiveGen;
                  DCOMP._IOwnership _1801___v140;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1802_recIdents;
                  RAST._IExpr _out306;
                  DCOMP._IOwnership _out307;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out308;
                  (this).GenExpr(_1779_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out306, out _out307, out _out308);
                  _1800_recursiveGen = _out306;
                  _1801___v140 = _out307;
                  _1802_recIdents = _out308;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1799_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1800_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out309;
                  DCOMP._IOwnership _out310;
                  (this).FromOwned(r, expectedOwnership, out _out309, out _out310);
                  r = _out309;
                  resultingOwnership = _out310;
                  readIdents = _1802_recIdents;
                }
                goto after_match40;
              }
            }
          }
        }
        {
          DAST._IType _04 = _source94.dtor__0;
          if (_04.is_Passthrough) {
            DAST._IType _14 = _source94.dtor__1;
            if (_14.is_Primitive) {
              DAST._IPrimitive _h77 = _14.dtor_Primitive_a0;
              if (_h77.is_Int) {
                {
                  RAST._IType _1803_rhsType;
                  RAST._IType _out311;
                  _out311 = (this).GenType(_1780_fromTpe, DCOMP.GenTypeContext.InBinding());
                  _1803_rhsType = _out311;
                  RAST._IExpr _1804_recursiveGen;
                  DCOMP._IOwnership _1805___v142;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1806_recIdents;
                  RAST._IExpr _out312;
                  DCOMP._IOwnership _out313;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out314;
                  (this).GenExpr(_1779_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out312, out _out313, out _out314);
                  _1804_recursiveGen = _out312;
                  _1805___v142 = _out313;
                  _1806_recIdents = _out314;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_1804_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out315;
                  DCOMP._IOwnership _out316;
                  (this).FromOwned(r, expectedOwnership, out _out315, out _out316);
                  r = _out315;
                  resultingOwnership = _out316;
                  readIdents = _1806_recIdents;
                }
                goto after_match40;
              }
            }
          }
        }
        {
          DAST._IType _05 = _source94.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h78 = _05.dtor_Primitive_a0;
            if (_h78.is_Int) {
              DAST._IType _15 = _source94.dtor__1;
              if (_15.is_Primitive) {
                DAST._IPrimitive _h79 = _15.dtor_Primitive_a0;
                if (_h79.is_Char) {
                  {
                    RAST._IType _1807_rhsType;
                    RAST._IType _out317;
                    _out317 = (this).GenType(_1781_toTpe, DCOMP.GenTypeContext.InBinding());
                    _1807_rhsType = _out317;
                    RAST._IExpr _1808_recursiveGen;
                    DCOMP._IOwnership _1809___v143;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1810_recIdents;
                    RAST._IExpr _out318;
                    DCOMP._IOwnership _out319;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out320;
                    (this).GenExpr(_1779_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out318, out _out319, out _out320);
                    _1808_recursiveGen = _out318;
                    _1809___v143 = _out319;
                    _1810_recIdents = _out320;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1808_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out321;
                    DCOMP._IOwnership _out322;
                    (this).FromOwned(r, expectedOwnership, out _out321, out _out322);
                    r = _out321;
                    resultingOwnership = _out322;
                    readIdents = _1810_recIdents;
                  }
                  goto after_match40;
                }
              }
            }
          }
        }
        {
          DAST._IType _06 = _source94.dtor__0;
          if (_06.is_Primitive) {
            DAST._IPrimitive _h710 = _06.dtor_Primitive_a0;
            if (_h710.is_Char) {
              DAST._IType _16 = _source94.dtor__1;
              if (_16.is_Primitive) {
                DAST._IPrimitive _h711 = _16.dtor_Primitive_a0;
                if (_h711.is_Int) {
                  {
                    RAST._IType _1811_rhsType;
                    RAST._IType _out323;
                    _out323 = (this).GenType(_1780_fromTpe, DCOMP.GenTypeContext.InBinding());
                    _1811_rhsType = _out323;
                    RAST._IExpr _1812_recursiveGen;
                    DCOMP._IOwnership _1813___v144;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1814_recIdents;
                    RAST._IExpr _out324;
                    DCOMP._IOwnership _out325;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out326;
                    (this).GenExpr(_1779_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out324, out _out325, out _out326);
                    _1812_recursiveGen = _out324;
                    _1813___v144 = _out325;
                    _1814_recIdents = _out326;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1812_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out327;
                    DCOMP._IOwnership _out328;
                    (this).FromOwned(r, expectedOwnership, out _out327, out _out328);
                    r = _out327;
                    resultingOwnership = _out328;
                    readIdents = _1814_recIdents;
                  }
                  goto after_match40;
                }
              }
            }
          }
        }
        {
          DAST._IType _07 = _source94.dtor__0;
          if (_07.is_Passthrough) {
            DAST._IType _17 = _source94.dtor__1;
            if (_17.is_Passthrough) {
              {
                RAST._IExpr _1815_recursiveGen;
                DCOMP._IOwnership _1816___v147;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1817_recIdents;
                RAST._IExpr _out329;
                DCOMP._IOwnership _out330;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
                (this).GenExpr(_1779_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out329, out _out330, out _out331);
                _1815_recursiveGen = _out329;
                _1816___v147 = _out330;
                _1817_recIdents = _out331;
                RAST._IType _1818_toTpeGen;
                RAST._IType _out332;
                _out332 = (this).GenType(_1781_toTpe, DCOMP.GenTypeContext.InBinding());
                _1818_toTpeGen = _out332;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1815_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1818_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out333;
                DCOMP._IOwnership _out334;
                (this).FromOwned(r, expectedOwnership, out _out333, out _out334);
                r = _out333;
                resultingOwnership = _out334;
                readIdents = _1817_recIdents;
              }
              goto after_match40;
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
      after_match40: ;
      }
      return ;
    }
    public void GenIdent(Dafny.ISequence<Dafny.Rune> rName, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      r = RAST.Expr.create_Identifier(rName);
      Std.Wrappers._IOption<RAST._IType> _1819_tpe;
      _1819_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1820_placeboOpt;
      if ((_1819_tpe).is_Some) {
        _1820_placeboOpt = ((_1819_tpe).dtor_value).ExtractMaybePlacebo();
      } else {
        _1820_placeboOpt = Std.Wrappers.Option<RAST._IType>.create_None();
      }
      bool _1821_currentlyBorrowed;
      _1821_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1822_noNeedOfClone;
      _1822_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1820_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _1821_currentlyBorrowed = false;
        _1822_noNeedOfClone = true;
        _1819_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_1820_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        if (_1821_currentlyBorrowed) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        } else {
          resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
        }
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_1819_tpe).is_Some) && (((_1819_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _1823_needObjectFromRef;
        _1823_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source95 = (selfIdent).dtor_dafnyType;
          {
            if (_source95.is_UserDefined) {
              DAST._IResolvedType resolved4 = _source95.dtor_resolved;
              DAST._IResolvedTypeBase _1824_base = resolved4.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _1825_attributes = resolved4.dtor_attributes;
              return ((_1824_base).is_Class) || ((_1824_base).is_Trait);
            }
          }
          {
            return false;
          }
        }))());
        if (_1823_needObjectFromRef) {
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_1822_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1822_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1821_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_1819_tpe).is_Some) && (((_1819_tpe).dtor_value).IsPointer())) {
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
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_1826_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_1826_attributes).UniqueElements, false, (((_exists_var_2) => {
        DAST._IAttribute _1827_attribute = (DAST._IAttribute)_exists_var_2;
        return ((_1826_attributes).Contains(_1827_attribute)) && ((((_1827_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_1827_attribute).dtor_args).Count)) == (new BigInteger(2))));
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
      BigInteger _hi38 = new BigInteger((args).Count);
      for (BigInteger _1828_i = BigInteger.Zero; _1828_i < _hi38; _1828_i++) {
        DCOMP._IOwnership _1829_argOwnership;
        _1829_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if (((name).is_CallName) && ((_1828_i) < (new BigInteger((((name).dtor_signature)).Count)))) {
          RAST._IType _1830_tpe;
          RAST._IType _out338;
          _out338 = (this).GenType(((((name).dtor_signature)).Select(_1828_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _1830_tpe = _out338;
          if ((_1830_tpe).CanReadWithoutClone()) {
            _1829_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _1831_argExpr;
        DCOMP._IOwnership _1832___v154;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1833_argIdents;
        RAST._IExpr _out339;
        DCOMP._IOwnership _out340;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out341;
        (this).GenExpr((args).Select(_1828_i), selfIdent, env, _1829_argOwnership, out _out339, out _out340, out _out341);
        _1831_argExpr = _out339;
        _1832___v154 = _out340;
        _1833_argIdents = _out341;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1831_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1833_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi39 = new BigInteger((typeArgs).Count);
      for (BigInteger _1834_typeI = BigInteger.Zero; _1834_typeI < _hi39; _1834_typeI++) {
        RAST._IType _1835_typeExpr;
        RAST._IType _out342;
        _out342 = (this).GenType((typeArgs).Select(_1834_typeI), DCOMP.GenTypeContext.@default());
        _1835_typeExpr = _out342;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1835_typeExpr));
      }
      DAST._ICallName _source96 = name;
      {
        if (_source96.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _1836_nameIdent = _source96.dtor_name;
          Std.Wrappers._IOption<DAST._IType> onType1 = _source96.dtor_onType;
          if (onType1.is_Some) {
            DAST._IType value10 = onType1.dtor_value;
            if (value10.is_UserDefined) {
              DAST._IResolvedType _1837_resolvedType = value10.dtor_resolved;
              if ((((_1837_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_1838_resolvedType, _1839_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(((_1838_resolvedType).dtor_properMethods).UniqueElements, true, (((_forall_var_8) => {
                Dafny.ISequence<Dafny.Rune> _1840_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_8;
                return !(((_1838_resolvedType).dtor_properMethods).Contains(_1840_m)) || (!object.Equals((_1840_m), _1839_nameIdent));
              }))))(_1837_resolvedType, _1836_nameIdent))) {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_1837_resolvedType, (_1836_nameIdent)), _1837_resolvedType));
              } else {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
              }
              goto after_match41;
            }
          }
        }
      }
      {
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
    after_match41: ;
      if ((((((fullNameQualifier).is_Some) && ((selfIdent).is_ThisTyped)) && (((selfIdent).dtor_dafnyType).is_UserDefined)) && ((this).IsSameResolvedType(((selfIdent).dtor_dafnyType).dtor_resolved, (fullNameQualifier).dtor_value))) && (!((this).HasExternAttributeRenamingModule(((fullNameQualifier).dtor_value).dtor_attributes)))) {
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
    }
    public void GenExpr(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source97 = e;
      {
        if (_source97.is_Literal) {
          RAST._IExpr _out343;
          DCOMP._IOwnership _out344;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out345;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out343, out _out344, out _out345);
          r = _out343;
          resultingOwnership = _out344;
          readIdents = _out345;
          goto after_match42;
        }
      }
      {
        if (_source97.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1841_name = _source97.dtor_name;
          {
            RAST._IExpr _out346;
            DCOMP._IOwnership _out347;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out348;
            (this).GenIdent(DCOMP.__default.escapeName(_1841_name), selfIdent, env, expectedOwnership, out _out346, out _out347, out _out348);
            r = _out346;
            resultingOwnership = _out347;
            readIdents = _out348;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1842_path = _source97.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _1843_typeArgs = _source97.dtor_typeArgs;
          {
            RAST._IExpr _out349;
            _out349 = DCOMP.COMP.GenPathExpr(_1842_path);
            r = _out349;
            if ((new BigInteger((_1843_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1844_typeExprs;
              _1844_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi40 = new BigInteger((_1843_typeArgs).Count);
              for (BigInteger _1845_i = BigInteger.Zero; _1845_i < _hi40; _1845_i++) {
                RAST._IType _1846_typeExpr;
                RAST._IType _out350;
                _out350 = (this).GenType((_1843_typeArgs).Select(_1845_i), DCOMP.GenTypeContext.@default());
                _1846_typeExpr = _out350;
                _1844_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1844_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1846_typeExpr));
              }
              r = (r).ApplyType(_1844_typeExprs);
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
          goto after_match42;
        }
      }
      {
        if (_source97.is_InitializationValue) {
          DAST._IType _1847_typ = _source97.dtor_typ;
          {
            RAST._IType _1848_typExpr;
            RAST._IType _out353;
            _out353 = (this).GenType(_1847_typ, DCOMP.GenTypeContext.@default());
            _1848_typExpr = _out353;
            if ((_1848_typExpr).IsObjectOrPointer()) {
              r = (_1848_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1848_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
            }
            RAST._IExpr _out354;
            DCOMP._IOwnership _out355;
            (this).FromOwned(r, expectedOwnership, out _out354, out _out355);
            r = _out354;
            resultingOwnership = _out355;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _1849_values = _source97.dtor_Tuple_a0;
          {
            Dafny.ISequence<RAST._IExpr> _1850_exprs;
            _1850_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi41 = new BigInteger((_1849_values).Count);
            for (BigInteger _1851_i = BigInteger.Zero; _1851_i < _hi41; _1851_i++) {
              RAST._IExpr _1852_recursiveGen;
              DCOMP._IOwnership _1853___v159;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1854_recIdents;
              RAST._IExpr _out356;
              DCOMP._IOwnership _out357;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out358;
              (this).GenExpr((_1849_values).Select(_1851_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out356, out _out357, out _out358);
              _1852_recursiveGen = _out356;
              _1853___v159 = _out357;
              _1854_recIdents = _out358;
              _1850_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1850_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1852_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1854_recIdents);
            }
            if ((new BigInteger((_1849_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) {
              r = RAST.Expr.create_Tuple(_1850_exprs);
            } else {
              r = RAST.__default.SystemTuple(_1850_exprs);
            }
            RAST._IExpr _out359;
            DCOMP._IOwnership _out360;
            (this).FromOwned(r, expectedOwnership, out _out359, out _out360);
            r = _out359;
            resultingOwnership = _out360;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1855_path = _source97.dtor_path;
          Dafny.ISequence<DAST._IType> _1856_typeArgs = _source97.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1857_args = _source97.dtor_args;
          {
            RAST._IExpr _out361;
            _out361 = DCOMP.COMP.GenPathExpr(_1855_path);
            r = _out361;
            if ((new BigInteger((_1856_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1858_typeExprs;
              _1858_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi42 = new BigInteger((_1856_typeArgs).Count);
              for (BigInteger _1859_i = BigInteger.Zero; _1859_i < _hi42; _1859_i++) {
                RAST._IType _1860_typeExpr;
                RAST._IType _out362;
                _out362 = (this).GenType((_1856_typeArgs).Select(_1859_i), DCOMP.GenTypeContext.@default());
                _1860_typeExpr = _out362;
                _1858_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1858_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1860_typeExpr));
              }
              r = (r).ApplyType(_1858_typeExprs);
            }
            r = (r).MSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1861_arguments;
            _1861_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi43 = new BigInteger((_1857_args).Count);
            for (BigInteger _1862_i = BigInteger.Zero; _1862_i < _hi43; _1862_i++) {
              RAST._IExpr _1863_recursiveGen;
              DCOMP._IOwnership _1864___v160;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1865_recIdents;
              RAST._IExpr _out363;
              DCOMP._IOwnership _out364;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out365;
              (this).GenExpr((_1857_args).Select(_1862_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out363, out _out364, out _out365);
              _1863_recursiveGen = _out363;
              _1864___v160 = _out364;
              _1865_recIdents = _out365;
              _1861_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1861_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1863_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1865_recIdents);
            }
            r = (r).Apply(_1861_arguments);
            RAST._IExpr _out366;
            DCOMP._IOwnership _out367;
            (this).FromOwned(r, expectedOwnership, out _out366, out _out367);
            r = _out366;
            resultingOwnership = _out367;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_NewUninitArray) {
          Dafny.ISequence<DAST._IExpression> _1866_dims = _source97.dtor_dims;
          DAST._IType _1867_typ = _source97.dtor_typ;
          {
            if ((new BigInteger(16)) < (new BigInteger((_1866_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _1868_msg;
              _1868_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1868_msg);
              }
              r = RAST.Expr.create_RawExpr(_1868_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _1869_typeGen;
              RAST._IType _out368;
              _out368 = (this).GenType(_1867_typ, DCOMP.GenTypeContext.@default());
              _1869_typeGen = _out368;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _1870_dimExprs;
              _1870_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi44 = new BigInteger((_1866_dims).Count);
              for (BigInteger _1871_i = BigInteger.Zero; _1871_i < _hi44; _1871_i++) {
                RAST._IExpr _1872_recursiveGen;
                DCOMP._IOwnership _1873___v161;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1874_recIdents;
                RAST._IExpr _out369;
                DCOMP._IOwnership _out370;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out371;
                (this).GenExpr((_1866_dims).Select(_1871_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out369, out _out370, out _out371);
                _1872_recursiveGen = _out369;
                _1873___v161 = _out370;
                _1874_recIdents = _out371;
                _1870_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1870_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.IntoUsize(_1872_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1874_recIdents);
              }
              if ((new BigInteger((_1866_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _1875_class__name;
                _1875_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_1866_dims).Count)));
                r = ((((RAST.__default.dafny__runtime).MSel(_1875_class__name)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1869_typeGen))).MSel((this).placebos__usize)).Apply(_1870_dimExprs);
              } else {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1869_typeGen))).Apply(_1870_dimExprs);
              }
            }
            RAST._IExpr _out372;
            DCOMP._IOwnership _out373;
            (this).FromOwned(r, expectedOwnership, out _out372, out _out373);
            r = _out372;
            resultingOwnership = _out373;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_ArrayIndexToInt) {
          DAST._IExpression _1876_underlying = _source97.dtor_value;
          {
            RAST._IExpr _1877_recursiveGen;
            DCOMP._IOwnership _1878___v162;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1879_recIdents;
            RAST._IExpr _out374;
            DCOMP._IOwnership _out375;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out376;
            (this).GenExpr(_1876_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out374, out _out375, out _out376);
            _1877_recursiveGen = _out374;
            _1878___v162 = _out375;
            _1879_recIdents = _out376;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(_1877_recursiveGen);
            readIdents = _1879_recIdents;
            RAST._IExpr _out377;
            DCOMP._IOwnership _out378;
            (this).FromOwned(r, expectedOwnership, out _out377, out _out378);
            r = _out377;
            resultingOwnership = _out378;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_FinalizeNewArray) {
          DAST._IExpression _1880_underlying = _source97.dtor_value;
          DAST._IType _1881_typ = _source97.dtor_typ;
          {
            RAST._IType _1882_tpe;
            RAST._IType _out379;
            _out379 = (this).GenType(_1881_typ, DCOMP.GenTypeContext.@default());
            _1882_tpe = _out379;
            RAST._IExpr _1883_recursiveGen;
            DCOMP._IOwnership _1884___v163;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1885_recIdents;
            RAST._IExpr _out380;
            DCOMP._IOwnership _out381;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out382;
            (this).GenExpr(_1880_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out380, out _out381, out _out382);
            _1883_recursiveGen = _out380;
            _1884___v163 = _out381;
            _1885_recIdents = _out382;
            readIdents = _1885_recIdents;
            if ((_1882_tpe).IsObjectOrPointer()) {
              RAST._IType _1886_t;
              _1886_t = (_1882_tpe).ObjectOrPointerUnderlying();
              if ((_1886_t).is_Array) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).array__construct)).Apply1(_1883_recursiveGen);
              } else if ((_1886_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _1887_c;
                _1887_c = (_1886_t).MultiArrayClass();
                r = (((RAST.__default.dafny__runtime).MSel(_1887_c)).MSel((this).array__construct)).Apply1(_1883_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_1882_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_1882_tpe)._ToString(DCOMP.__default.IND)));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            }
            RAST._IExpr _out383;
            DCOMP._IOwnership _out384;
            (this).FromOwned(r, expectedOwnership, out _out383, out _out384);
            r = _out383;
            resultingOwnership = _out384;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_DatatypeValue) {
          DAST._IResolvedType _1888_datatypeType = _source97.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1889_typeArgs = _source97.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1890_variant = _source97.dtor_variant;
          bool _1891_isCo = _source97.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1892_values = _source97.dtor_contents;
          {
            RAST._IExpr _out385;
            _out385 = DCOMP.COMP.GenPathExpr((_1888_datatypeType).dtor_path);
            r = _out385;
            Dafny.ISequence<RAST._IType> _1893_genTypeArgs;
            _1893_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi45 = new BigInteger((_1889_typeArgs).Count);
            for (BigInteger _1894_i = BigInteger.Zero; _1894_i < _hi45; _1894_i++) {
              RAST._IType _1895_typeExpr;
              RAST._IType _out386;
              _out386 = (this).GenType((_1889_typeArgs).Select(_1894_i), DCOMP.GenTypeContext.@default());
              _1895_typeExpr = _out386;
              _1893_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1893_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1895_typeExpr));
            }
            if ((new BigInteger((_1889_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1893_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1890_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1896_assignments;
            _1896_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi46 = new BigInteger((_1892_values).Count);
            for (BigInteger _1897_i = BigInteger.Zero; _1897_i < _hi46; _1897_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs67 = (_1892_values).Select(_1897_i);
              Dafny.ISequence<Dafny.Rune> _1898_name = _let_tmp_rhs67.dtor__0;
              DAST._IExpression _1899_value = _let_tmp_rhs67.dtor__1;
              if (_1891_isCo) {
                RAST._IExpr _1900_recursiveGen;
                DCOMP._IOwnership _1901___v164;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1902_recIdents;
                RAST._IExpr _out387;
                DCOMP._IOwnership _out388;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out389;
                (this).GenExpr(_1899_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out387, out _out388, out _out389);
                _1900_recursiveGen = _out387;
                _1901___v164 = _out388;
                _1902_recIdents = _out389;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1902_recIdents);
                Dafny.ISequence<Dafny.Rune> _1903_allReadCloned;
                _1903_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1902_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1904_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1902_recIdents).Elements) {
                    _1904_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1902_recIdents).Contains(_1904_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4433)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1903_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1903_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1904_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1904_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1902_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1902_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1904_next));
                }
                Dafny.ISequence<Dafny.Rune> _1905_wasAssigned;
                _1905_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1903_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1900_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1896_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1896_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1898_name), RAST.Expr.create_RawExpr(_1905_wasAssigned))));
              } else {
                RAST._IExpr _1906_recursiveGen;
                DCOMP._IOwnership _1907___v165;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1908_recIdents;
                RAST._IExpr _out390;
                DCOMP._IOwnership _out391;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out392;
                (this).GenExpr(_1899_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out390, out _out391, out _out392);
                _1906_recursiveGen = _out390;
                _1907___v165 = _out391;
                _1908_recIdents = _out392;
                _1896_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1896_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1898_name), _1906_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1908_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1896_assignments);
            if ((this).IsRcWrapped((_1888_datatypeType).dtor_attributes)) {
              r = RAST.__default.RcNew(r);
            }
            RAST._IExpr _out393;
            DCOMP._IOwnership _out394;
            (this).FromOwned(r, expectedOwnership, out _out393, out _out394);
            r = _out393;
            resultingOwnership = _out394;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_Convert) {
          {
            RAST._IExpr _out395;
            DCOMP._IOwnership _out396;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out397;
            (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out395, out _out396, out _out397);
            r = _out395;
            resultingOwnership = _out396;
            readIdents = _out397;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_SeqConstruct) {
          DAST._IExpression _1909_length = _source97.dtor_length;
          DAST._IExpression _1910_expr = _source97.dtor_elem;
          {
            RAST._IExpr _1911_recursiveGen;
            DCOMP._IOwnership _1912___v169;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1913_recIdents;
            RAST._IExpr _out398;
            DCOMP._IOwnership _out399;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out400;
            (this).GenExpr(_1910_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out398, out _out399, out _out400);
            _1911_recursiveGen = _out398;
            _1912___v169 = _out399;
            _1913_recIdents = _out400;
            RAST._IExpr _1914_lengthGen;
            DCOMP._IOwnership _1915___v170;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1916_lengthIdents;
            RAST._IExpr _out401;
            DCOMP._IOwnership _out402;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
            (this).GenExpr(_1909_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out401, out _out402, out _out403);
            _1914_lengthGen = _out401;
            _1915___v170 = _out402;
            _1916_lengthIdents = _out403;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1911_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1914_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1913_recIdents, _1916_lengthIdents);
            RAST._IExpr _out404;
            DCOMP._IOwnership _out405;
            (this).FromOwned(r, expectedOwnership, out _out404, out _out405);
            r = _out404;
            resultingOwnership = _out405;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _1917_exprs = _source97.dtor_elements;
          DAST._IType _1918_typ = _source97.dtor_typ;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1919_genTpe;
            RAST._IType _out406;
            _out406 = (this).GenType(_1918_typ, DCOMP.GenTypeContext.@default());
            _1919_genTpe = _out406;
            BigInteger _1920_i;
            _1920_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1921_args;
            _1921_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1920_i) < (new BigInteger((_1917_exprs).Count))) {
              RAST._IExpr _1922_recursiveGen;
              DCOMP._IOwnership _1923___v171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1924_recIdents;
              RAST._IExpr _out407;
              DCOMP._IOwnership _out408;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
              (this).GenExpr((_1917_exprs).Select(_1920_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out407, out _out408, out _out409);
              _1922_recursiveGen = _out407;
              _1923___v171 = _out408;
              _1924_recIdents = _out409;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1924_recIdents);
              _1921_args = Dafny.Sequence<RAST._IExpr>.Concat(_1921_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1922_recursiveGen));
              _1920_i = (_1920_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_1921_args);
            if ((new BigInteger((_1921_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1919_genTpe));
            }
            RAST._IExpr _out410;
            DCOMP._IOwnership _out411;
            (this).FromOwned(r, expectedOwnership, out _out410, out _out411);
            r = _out410;
            resultingOwnership = _out411;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _1925_exprs = _source97.dtor_elements;
          {
            Dafny.ISequence<RAST._IExpr> _1926_generatedValues;
            _1926_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1927_i;
            _1927_i = BigInteger.Zero;
            while ((_1927_i) < (new BigInteger((_1925_exprs).Count))) {
              RAST._IExpr _1928_recursiveGen;
              DCOMP._IOwnership _1929___v172;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1930_recIdents;
              RAST._IExpr _out412;
              DCOMP._IOwnership _out413;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out414;
              (this).GenExpr((_1925_exprs).Select(_1927_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out412, out _out413, out _out414);
              _1928_recursiveGen = _out412;
              _1929___v172 = _out413;
              _1930_recIdents = _out414;
              _1926_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1926_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1928_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1930_recIdents);
              _1927_i = (_1927_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_1926_generatedValues);
            RAST._IExpr _out415;
            DCOMP._IOwnership _out416;
            (this).FromOwned(r, expectedOwnership, out _out415, out _out416);
            r = _out415;
            resultingOwnership = _out416;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _1931_exprs = _source97.dtor_elements;
          {
            Dafny.ISequence<RAST._IExpr> _1932_generatedValues;
            _1932_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1933_i;
            _1933_i = BigInteger.Zero;
            while ((_1933_i) < (new BigInteger((_1931_exprs).Count))) {
              RAST._IExpr _1934_recursiveGen;
              DCOMP._IOwnership _1935___v173;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1936_recIdents;
              RAST._IExpr _out417;
              DCOMP._IOwnership _out418;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out419;
              (this).GenExpr((_1931_exprs).Select(_1933_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out417, out _out418, out _out419);
              _1934_recursiveGen = _out417;
              _1935___v173 = _out418;
              _1936_recIdents = _out419;
              _1932_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1932_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1934_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1936_recIdents);
              _1933_i = (_1933_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_1932_generatedValues);
            RAST._IExpr _out420;
            DCOMP._IOwnership _out421;
            (this).FromOwned(r, expectedOwnership, out _out420, out _out421);
            r = _out420;
            resultingOwnership = _out421;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_ToMultiset) {
          DAST._IExpression _1937_expr = _source97.dtor_ToMultiset_a0;
          {
            RAST._IExpr _1938_recursiveGen;
            DCOMP._IOwnership _1939___v174;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1940_recIdents;
            RAST._IExpr _out422;
            DCOMP._IOwnership _out423;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out424;
            (this).GenExpr(_1937_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out422, out _out423, out _out424);
            _1938_recursiveGen = _out422;
            _1939___v174 = _out423;
            _1940_recIdents = _out424;
            r = ((_1938_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _1940_recIdents;
            RAST._IExpr _out425;
            DCOMP._IOwnership _out426;
            (this).FromOwned(r, expectedOwnership, out _out425, out _out426);
            r = _out425;
            resultingOwnership = _out426;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1941_mapElems = _source97.dtor_mapElems;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1942_generatedValues;
            _1942_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1943_i;
            _1943_i = BigInteger.Zero;
            while ((_1943_i) < (new BigInteger((_1941_mapElems).Count))) {
              RAST._IExpr _1944_recursiveGenKey;
              DCOMP._IOwnership _1945___v175;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1946_recIdentsKey;
              RAST._IExpr _out427;
              DCOMP._IOwnership _out428;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out429;
              (this).GenExpr(((_1941_mapElems).Select(_1943_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out427, out _out428, out _out429);
              _1944_recursiveGenKey = _out427;
              _1945___v175 = _out428;
              _1946_recIdentsKey = _out429;
              RAST._IExpr _1947_recursiveGenValue;
              DCOMP._IOwnership _1948___v176;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1949_recIdentsValue;
              RAST._IExpr _out430;
              DCOMP._IOwnership _out431;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out432;
              (this).GenExpr(((_1941_mapElems).Select(_1943_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out430, out _out431, out _out432);
              _1947_recursiveGenValue = _out430;
              _1948___v176 = _out431;
              _1949_recIdentsValue = _out432;
              _1942_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1942_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1944_recursiveGenKey, _1947_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1946_recIdentsKey), _1949_recIdentsValue);
              _1943_i = (_1943_i) + (BigInteger.One);
            }
            _1943_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1950_arguments;
            _1950_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1943_i) < (new BigInteger((_1942_generatedValues).Count))) {
              RAST._IExpr _1951_genKey;
              _1951_genKey = ((_1942_generatedValues).Select(_1943_i)).dtor__0;
              RAST._IExpr _1952_genValue;
              _1952_genValue = ((_1942_generatedValues).Select(_1943_i)).dtor__1;
              _1950_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1950_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1951_genKey, _1952_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _1943_i = (_1943_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_1950_arguments);
            RAST._IExpr _out433;
            DCOMP._IOwnership _out434;
            (this).FromOwned(r, expectedOwnership, out _out433, out _out434);
            r = _out433;
            resultingOwnership = _out434;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_SeqUpdate) {
          DAST._IExpression _1953_expr = _source97.dtor_expr;
          DAST._IExpression _1954_index = _source97.dtor_indexExpr;
          DAST._IExpression _1955_value = _source97.dtor_value;
          {
            RAST._IExpr _1956_exprR;
            DCOMP._IOwnership _1957___v177;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1958_exprIdents;
            RAST._IExpr _out435;
            DCOMP._IOwnership _out436;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out437;
            (this).GenExpr(_1953_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out435, out _out436, out _out437);
            _1956_exprR = _out435;
            _1957___v177 = _out436;
            _1958_exprIdents = _out437;
            RAST._IExpr _1959_indexR;
            DCOMP._IOwnership _1960_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1961_indexIdents;
            RAST._IExpr _out438;
            DCOMP._IOwnership _out439;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out440;
            (this).GenExpr(_1954_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out438, out _out439, out _out440);
            _1959_indexR = _out438;
            _1960_indexOwnership = _out439;
            _1961_indexIdents = _out440;
            RAST._IExpr _1962_valueR;
            DCOMP._IOwnership _1963_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1964_valueIdents;
            RAST._IExpr _out441;
            DCOMP._IOwnership _out442;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out443;
            (this).GenExpr(_1955_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out441, out _out442, out _out443);
            _1962_valueR = _out441;
            _1963_valueOwnership = _out442;
            _1964_valueIdents = _out443;
            r = ((_1956_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1959_indexR, _1962_valueR));
            RAST._IExpr _out444;
            DCOMP._IOwnership _out445;
            (this).FromOwned(r, expectedOwnership, out _out444, out _out445);
            r = _out444;
            resultingOwnership = _out445;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1958_exprIdents, _1961_indexIdents), _1964_valueIdents);
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_MapUpdate) {
          DAST._IExpression _1965_expr = _source97.dtor_expr;
          DAST._IExpression _1966_index = _source97.dtor_indexExpr;
          DAST._IExpression _1967_value = _source97.dtor_value;
          {
            RAST._IExpr _1968_exprR;
            DCOMP._IOwnership _1969___v178;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1970_exprIdents;
            RAST._IExpr _out446;
            DCOMP._IOwnership _out447;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out448;
            (this).GenExpr(_1965_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out446, out _out447, out _out448);
            _1968_exprR = _out446;
            _1969___v178 = _out447;
            _1970_exprIdents = _out448;
            RAST._IExpr _1971_indexR;
            DCOMP._IOwnership _1972_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1973_indexIdents;
            RAST._IExpr _out449;
            DCOMP._IOwnership _out450;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
            (this).GenExpr(_1966_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out449, out _out450, out _out451);
            _1971_indexR = _out449;
            _1972_indexOwnership = _out450;
            _1973_indexIdents = _out451;
            RAST._IExpr _1974_valueR;
            DCOMP._IOwnership _1975_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1976_valueIdents;
            RAST._IExpr _out452;
            DCOMP._IOwnership _out453;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out454;
            (this).GenExpr(_1967_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out452, out _out453, out _out454);
            _1974_valueR = _out452;
            _1975_valueOwnership = _out453;
            _1976_valueIdents = _out454;
            r = ((_1968_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1971_indexR, _1974_valueR));
            RAST._IExpr _out455;
            DCOMP._IOwnership _out456;
            (this).FromOwned(r, expectedOwnership, out _out455, out _out456);
            r = _out455;
            resultingOwnership = _out456;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1970_exprIdents, _1973_indexIdents), _1976_valueIdents);
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_This) {
          {
            DCOMP._ISelfInfo _source98 = selfIdent;
            {
              if (_source98.is_ThisTyped) {
                Dafny.ISequence<Dafny.Rune> _1977_id = _source98.dtor_rSelfName;
                DAST._IType _1978_dafnyType = _source98.dtor_dafnyType;
                {
                  RAST._IExpr _out457;
                  DCOMP._IOwnership _out458;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out459;
                  (this).GenIdent(_1977_id, selfIdent, env, expectedOwnership, out _out457, out _out458, out _out459);
                  r = _out457;
                  resultingOwnership = _out458;
                  readIdents = _out459;
                }
                goto after_match43;
              }
            }
            {
              DCOMP._ISelfInfo _1979_None = _source98;
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
          after_match43: ;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_Ite) {
          DAST._IExpression _1980_cond = _source97.dtor_cond;
          DAST._IExpression _1981_t = _source97.dtor_thn;
          DAST._IExpression _1982_f = _source97.dtor_els;
          {
            RAST._IExpr _1983_cond;
            DCOMP._IOwnership _1984___v179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1985_recIdentsCond;
            RAST._IExpr _out462;
            DCOMP._IOwnership _out463;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out464;
            (this).GenExpr(_1980_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out462, out _out463, out _out464);
            _1983_cond = _out462;
            _1984___v179 = _out463;
            _1985_recIdentsCond = _out464;
            RAST._IExpr _1986_fExpr;
            DCOMP._IOwnership _1987_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1988_recIdentsF;
            RAST._IExpr _out465;
            DCOMP._IOwnership _out466;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out467;
            (this).GenExpr(_1982_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out465, out _out466, out _out467);
            _1986_fExpr = _out465;
            _1987_fOwned = _out466;
            _1988_recIdentsF = _out467;
            RAST._IExpr _1989_tExpr;
            DCOMP._IOwnership _1990___v180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1991_recIdentsT;
            RAST._IExpr _out468;
            DCOMP._IOwnership _out469;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out470;
            (this).GenExpr(_1981_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out468, out _out469, out _out470);
            _1989_tExpr = _out468;
            _1990___v180 = _out469;
            _1991_recIdentsT = _out470;
            r = RAST.Expr.create_IfExpr(_1983_cond, _1989_tExpr, _1986_fExpr);
            RAST._IExpr _out471;
            DCOMP._IOwnership _out472;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out471, out _out472);
            r = _out471;
            resultingOwnership = _out472;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1985_recIdentsCond, _1991_recIdentsT), _1988_recIdentsF);
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source97.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _1992_e = _source97.dtor_expr;
            DAST.Format._IUnaryOpFormat _1993_format = _source97.dtor_format1;
            {
              RAST._IExpr _1994_recursiveGen;
              DCOMP._IOwnership _1995___v181;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1996_recIdents;
              RAST._IExpr _out473;
              DCOMP._IOwnership _out474;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out475;
              (this).GenExpr(_1992_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out473, out _out474, out _out475);
              _1994_recursiveGen = _out473;
              _1995___v181 = _out474;
              _1996_recIdents = _out475;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _1994_recursiveGen, _1993_format);
              RAST._IExpr _out476;
              DCOMP._IOwnership _out477;
              (this).FromOwned(r, expectedOwnership, out _out476, out _out477);
              r = _out476;
              resultingOwnership = _out477;
              readIdents = _1996_recIdents;
              return ;
            }
            goto after_match42;
          }
        }
      }
      {
        if (_source97.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source97.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _1997_e = _source97.dtor_expr;
            DAST.Format._IUnaryOpFormat _1998_format = _source97.dtor_format1;
            {
              RAST._IExpr _1999_recursiveGen;
              DCOMP._IOwnership _2000___v182;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2001_recIdents;
              RAST._IExpr _out478;
              DCOMP._IOwnership _out479;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out480;
              (this).GenExpr(_1997_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out478, out _out479, out _out480);
              _1999_recursiveGen = _out478;
              _2000___v182 = _out479;
              _2001_recIdents = _out480;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _1999_recursiveGen, _1998_format);
              RAST._IExpr _out481;
              DCOMP._IOwnership _out482;
              (this).FromOwned(r, expectedOwnership, out _out481, out _out482);
              r = _out481;
              resultingOwnership = _out482;
              readIdents = _2001_recIdents;
              return ;
            }
            goto after_match42;
          }
        }
      }
      {
        if (_source97.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source97.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _2002_e = _source97.dtor_expr;
            DAST.Format._IUnaryOpFormat _2003_format = _source97.dtor_format1;
            {
              RAST._IExpr _2004_recursiveGen;
              DCOMP._IOwnership _2005_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2006_recIdents;
              RAST._IExpr _out483;
              DCOMP._IOwnership _out484;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out485;
              (this).GenExpr(_2002_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out483, out _out484, out _out485);
              _2004_recursiveGen = _out483;
              _2005_recOwned = _out484;
              _2006_recIdents = _out485;
              r = ((_2004_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out486;
              DCOMP._IOwnership _out487;
              (this).FromOwned(r, expectedOwnership, out _out486, out _out487);
              r = _out486;
              resultingOwnership = _out487;
              readIdents = _2006_recIdents;
              return ;
            }
            goto after_match42;
          }
        }
      }
      {
        if (_source97.is_BinOp) {
          RAST._IExpr _out488;
          DCOMP._IOwnership _out489;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out490;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out488, out _out489, out _out490);
          r = _out488;
          resultingOwnership = _out489;
          readIdents = _out490;
          goto after_match42;
        }
      }
      {
        if (_source97.is_ArrayLen) {
          DAST._IExpression _2007_expr = _source97.dtor_expr;
          DAST._IType _2008_exprType = _source97.dtor_exprType;
          BigInteger _2009_dim = _source97.dtor_dim;
          bool _2010_native = _source97.dtor_native;
          {
            RAST._IExpr _2011_recursiveGen;
            DCOMP._IOwnership _2012___v187;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2013_recIdents;
            RAST._IExpr _out491;
            DCOMP._IOwnership _out492;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out493;
            (this).GenExpr(_2007_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out491, out _out492, out _out493);
            _2011_recursiveGen = _out491;
            _2012___v187 = _out492;
            _2013_recIdents = _out493;
            RAST._IType _2014_arrayType;
            RAST._IType _out494;
            _out494 = (this).GenType(_2008_exprType, DCOMP.GenTypeContext.@default());
            _2014_arrayType = _out494;
            if (!((_2014_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _2015_msg;
              _2015_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_2014_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2015_msg);
              r = RAST.Expr.create_RawExpr(_2015_msg);
            } else {
              RAST._IType _2016_underlying;
              _2016_underlying = (_2014_arrayType).ObjectOrPointerUnderlying();
              if (((_2009_dim).Sign == 0) && ((_2016_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_2011_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_2009_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_2011_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = ((((this).read__macro).Apply1(_2011_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("length"), Std.Strings.__default.OfNat(_2009_dim)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_usize")))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                }
              }
              if (!(_2010_native)) {
                r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(r);
              }
            }
            RAST._IExpr _out495;
            DCOMP._IOwnership _out496;
            (this).FromOwned(r, expectedOwnership, out _out495, out _out496);
            r = _out495;
            resultingOwnership = _out496;
            readIdents = _2013_recIdents;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_MapKeys) {
          DAST._IExpression _2017_expr = _source97.dtor_expr;
          {
            RAST._IExpr _2018_recursiveGen;
            DCOMP._IOwnership _2019___v188;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2020_recIdents;
            RAST._IExpr _out497;
            DCOMP._IOwnership _out498;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out499;
            (this).GenExpr(_2017_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out497, out _out498, out _out499);
            _2018_recursiveGen = _out497;
            _2019___v188 = _out498;
            _2020_recIdents = _out499;
            readIdents = _2020_recIdents;
            r = ((_2018_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out500;
            DCOMP._IOwnership _out501;
            (this).FromOwned(r, expectedOwnership, out _out500, out _out501);
            r = _out500;
            resultingOwnership = _out501;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_MapValues) {
          DAST._IExpression _2021_expr = _source97.dtor_expr;
          {
            RAST._IExpr _2022_recursiveGen;
            DCOMP._IOwnership _2023___v189;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2024_recIdents;
            RAST._IExpr _out502;
            DCOMP._IOwnership _out503;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out504;
            (this).GenExpr(_2021_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out502, out _out503, out _out504);
            _2022_recursiveGen = _out502;
            _2023___v189 = _out503;
            _2024_recIdents = _out504;
            readIdents = _2024_recIdents;
            r = ((_2022_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out505;
            DCOMP._IOwnership _out506;
            (this).FromOwned(r, expectedOwnership, out _out505, out _out506);
            r = _out505;
            resultingOwnership = _out506;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_SelectFn) {
          DAST._IExpression _2025_on = _source97.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2026_field = _source97.dtor_field;
          bool _2027_isDatatype = _source97.dtor_onDatatype;
          bool _2028_isStatic = _source97.dtor_isStatic;
          BigInteger _2029_arity = _source97.dtor_arity;
          {
            RAST._IExpr _2030_onExpr;
            DCOMP._IOwnership _2031_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2032_recIdents;
            RAST._IExpr _out507;
            DCOMP._IOwnership _out508;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out509;
            (this).GenExpr(_2025_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out507, out _out508, out _out509);
            _2030_onExpr = _out507;
            _2031_onOwned = _out508;
            _2032_recIdents = _out509;
            Dafny.ISequence<Dafny.Rune> _2033_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _2034_onString;
            _2034_onString = (_2030_onExpr)._ToString(DCOMP.__default.IND);
            if (_2028_isStatic) {
              _2033_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2034_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_2026_field));
            } else {
              _2033_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _2033_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2033_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2034_onString), ((object.Equals(_2031_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _2035_args;
              _2035_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _2036_i;
              _2036_i = BigInteger.Zero;
              while ((_2036_i) < (_2029_arity)) {
                if ((_2036_i).Sign == 1) {
                  _2035_args = Dafny.Sequence<Dafny.Rune>.Concat(_2035_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _2035_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2035_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_2036_i));
                _2036_i = (_2036_i) + (BigInteger.One);
              }
              _2033_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2033_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2035_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _2033_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2033_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_2026_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2035_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _2033_s = Dafny.Sequence<Dafny.Rune>.Concat(_2033_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _2033_s = Dafny.Sequence<Dafny.Rune>.Concat(_2033_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _2037_typeShape;
            _2037_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _2038_i;
            _2038_i = BigInteger.Zero;
            while ((_2038_i) < (_2029_arity)) {
              if ((_2038_i).Sign == 1) {
                _2037_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2037_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2037_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2037_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _2038_i = (_2038_i) + (BigInteger.One);
            }
            _2037_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2037_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _2033_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _2033_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _2037_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_2033_s);
            RAST._IExpr _out510;
            DCOMP._IOwnership _out511;
            (this).FromOwned(r, expectedOwnership, out _out510, out _out511);
            r = _out510;
            resultingOwnership = _out511;
            readIdents = _2032_recIdents;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_Select) {
          DAST._IExpression expr0 = _source97.dtor_expr;
          if (expr0.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2039_c = expr0.dtor_Companion_a0;
            Dafny.ISequence<DAST._IType> _2040_typeArgs = expr0.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _2041_field = _source97.dtor_field;
            bool _2042_isConstant = _source97.dtor_isConstant;
            bool _2043_isDatatype = _source97.dtor_onDatatype;
            DAST._IType _2044_fieldType = _source97.dtor_fieldType;
            {
              RAST._IExpr _2045_onExpr;
              DCOMP._IOwnership _2046_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2047_recIdents;
              RAST._IExpr _out512;
              DCOMP._IOwnership _out513;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out514;
              (this).GenExpr(DAST.Expression.create_Companion(_2039_c, _2040_typeArgs), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out512, out _out513, out _out514);
              _2045_onExpr = _out512;
              _2046_onOwned = _out513;
              _2047_recIdents = _out514;
              r = ((_2045_onExpr).MSel(DCOMP.__default.escapeName(_2041_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out515;
              DCOMP._IOwnership _out516;
              (this).FromOwned(r, expectedOwnership, out _out515, out _out516);
              r = _out515;
              resultingOwnership = _out516;
              readIdents = _2047_recIdents;
              return ;
            }
            goto after_match42;
          }
        }
      }
      {
        if (_source97.is_Select) {
          DAST._IExpression _2048_on = _source97.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2049_field = _source97.dtor_field;
          bool _2050_isConstant = _source97.dtor_isConstant;
          bool _2051_isDatatype = _source97.dtor_onDatatype;
          DAST._IType _2052_fieldType = _source97.dtor_fieldType;
          {
            if (_2051_isDatatype) {
              RAST._IExpr _2053_onExpr;
              DCOMP._IOwnership _2054_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2055_recIdents;
              RAST._IExpr _out517;
              DCOMP._IOwnership _out518;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out519;
              (this).GenExpr(_2048_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out517, out _out518, out _out519);
              _2053_onExpr = _out517;
              _2054_onOwned = _out518;
              _2055_recIdents = _out519;
              r = ((_2053_onExpr).Sel(DCOMP.__default.escapeName(_2049_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _2056_typ;
              RAST._IType _out520;
              _out520 = (this).GenType(_2052_fieldType, DCOMP.GenTypeContext.@default());
              _2056_typ = _out520;
              RAST._IExpr _out521;
              DCOMP._IOwnership _out522;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out521, out _out522);
              r = _out521;
              resultingOwnership = _out522;
              readIdents = _2055_recIdents;
            } else {
              RAST._IExpr _2057_onExpr;
              DCOMP._IOwnership _2058_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2059_recIdents;
              RAST._IExpr _out523;
              DCOMP._IOwnership _out524;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
              (this).GenExpr(_2048_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out523, out _out524, out _out525);
              _2057_onExpr = _out523;
              _2058_onOwned = _out524;
              _2059_recIdents = _out525;
              r = _2057_onExpr;
              if (!object.Equals(_2057_onExpr, RAST.__default.self)) {
                RAST._IExpr _source99 = _2057_onExpr;
                {
                  if (_source99.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> op15 = _source99.dtor_op1;
                    if (object.Equals(op15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                      RAST._IExpr underlying5 = _source99.dtor_underlying;
                      if (underlying5.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name15 = underlying5.dtor_name;
                        if (object.Equals(name15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
                          goto after_match44;
                        }
                      }
                    }
                  }
                }
                {
                }
              after_match44: ;
                if (((this).ObjectType).is_RcMut) {
                  r = (r).Clone();
                }
                r = ((this).read__macro).Apply1(r);
              }
              r = (r).Sel(DCOMP.__default.escapeName(_2049_field));
              if (_2050_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out526;
              DCOMP._IOwnership _out527;
              (this).FromOwned(r, expectedOwnership, out _out526, out _out527);
              r = _out526;
              resultingOwnership = _out527;
              readIdents = _2059_recIdents;
            }
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_Index) {
          DAST._IExpression _2060_on = _source97.dtor_expr;
          DAST._ICollKind _2061_collKind = _source97.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2062_indices = _source97.dtor_indices;
          {
            RAST._IExpr _2063_onExpr;
            DCOMP._IOwnership _2064_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2065_recIdents;
            RAST._IExpr _out528;
            DCOMP._IOwnership _out529;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out530;
            (this).GenExpr(_2060_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out528, out _out529, out _out530);
            _2063_onExpr = _out528;
            _2064_onOwned = _out529;
            _2065_recIdents = _out530;
            readIdents = _2065_recIdents;
            r = _2063_onExpr;
            bool _2066_hadArray;
            _2066_hadArray = false;
            if (object.Equals(_2061_collKind, DAST.CollKind.create_Array())) {
              r = ((this).read__macro).Apply1(r);
              _2066_hadArray = true;
              if ((new BigInteger((_2062_indices).Count)) > (BigInteger.One)) {
                r = (r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
              }
            }
            BigInteger _hi47 = new BigInteger((_2062_indices).Count);
            for (BigInteger _2067_i = BigInteger.Zero; _2067_i < _hi47; _2067_i++) {
              if (object.Equals(_2061_collKind, DAST.CollKind.create_Array())) {
                RAST._IExpr _2068_idx;
                DCOMP._IOwnership _2069_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2070_recIdentsIdx;
                RAST._IExpr _out531;
                DCOMP._IOwnership _out532;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out533;
                (this).GenExpr((_2062_indices).Select(_2067_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out531, out _out532, out _out533);
                _2068_idx = _out531;
                _2069_idxOwned = _out532;
                _2070_recIdentsIdx = _out533;
                _2068_idx = RAST.__default.IntoUsize(_2068_idx);
                r = RAST.Expr.create_SelectIndex(r, _2068_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2070_recIdentsIdx);
              } else {
                RAST._IExpr _2071_idx;
                DCOMP._IOwnership _2072_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2073_recIdentsIdx;
                RAST._IExpr _out534;
                DCOMP._IOwnership _out535;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out536;
                (this).GenExpr((_2062_indices).Select(_2067_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out534, out _out535, out _out536);
                _2071_idx = _out534;
                _2072_idxOwned = _out535;
                _2073_recIdentsIdx = _out536;
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_2071_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2073_recIdentsIdx);
              }
            }
            if (_2066_hadArray) {
              r = (r).Clone();
            }
            RAST._IExpr _out537;
            DCOMP._IOwnership _out538;
            (this).FromOwned(r, expectedOwnership, out _out537, out _out538);
            r = _out537;
            resultingOwnership = _out538;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_IndexRange) {
          DAST._IExpression _2074_on = _source97.dtor_expr;
          bool _2075_isArray = _source97.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _2076_low = _source97.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _2077_high = _source97.dtor_high;
          {
            RAST._IExpr _2078_onExpr;
            DCOMP._IOwnership _2079_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2080_recIdents;
            RAST._IExpr _out539;
            DCOMP._IOwnership _out540;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
            (this).GenExpr(_2074_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out539, out _out540, out _out541);
            _2078_onExpr = _out539;
            _2079_onOwned = _out540;
            _2080_recIdents = _out541;
            readIdents = _2080_recIdents;
            Dafny.ISequence<Dafny.Rune> _2081_methodName;
            if ((_2076_low).is_Some) {
              if ((_2077_high).is_Some) {
                _2081_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice");
              } else {
                _2081_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop");
              }
            } else if ((_2077_high).is_Some) {
              _2081_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take");
            } else {
              _2081_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            }
            Dafny.ISequence<RAST._IExpr> _2082_arguments;
            _2082_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source100 = _2076_low;
            {
              if (_source100.is_Some) {
                DAST._IExpression _2083_l = _source100.dtor_value;
                {
                  RAST._IExpr _2084_lExpr;
                  DCOMP._IOwnership _2085___v192;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2086_recIdentsL;
                  RAST._IExpr _out542;
                  DCOMP._IOwnership _out543;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out544;
                  (this).GenExpr(_2083_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out542, out _out543, out _out544);
                  _2084_lExpr = _out542;
                  _2085___v192 = _out543;
                  _2086_recIdentsL = _out544;
                  _2082_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2082_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2084_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2086_recIdentsL);
                }
                goto after_match45;
              }
            }
            {
            }
          after_match45: ;
            Std.Wrappers._IOption<DAST._IExpression> _source101 = _2077_high;
            {
              if (_source101.is_Some) {
                DAST._IExpression _2087_h = _source101.dtor_value;
                {
                  RAST._IExpr _2088_hExpr;
                  DCOMP._IOwnership _2089___v193;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2090_recIdentsH;
                  RAST._IExpr _out545;
                  DCOMP._IOwnership _out546;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out547;
                  (this).GenExpr(_2087_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out545, out _out546, out _out547);
                  _2088_hExpr = _out545;
                  _2089___v193 = _out546;
                  _2090_recIdentsH = _out547;
                  _2082_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2082_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2088_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2090_recIdentsH);
                }
                goto after_match46;
              }
            }
            {
            }
          after_match46: ;
            r = _2078_onExpr;
            if (_2075_isArray) {
              if (!(_2081_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _2081_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2081_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _2081_methodName))).Apply(_2082_arguments);
            } else {
              if (!(_2081_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_2081_methodName)).Apply(_2082_arguments);
              }
            }
            RAST._IExpr _out548;
            DCOMP._IOwnership _out549;
            (this).FromOwned(r, expectedOwnership, out _out548, out _out549);
            r = _out548;
            resultingOwnership = _out549;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_TupleSelect) {
          DAST._IExpression _2091_on = _source97.dtor_expr;
          BigInteger _2092_idx = _source97.dtor_index;
          DAST._IType _2093_fieldType = _source97.dtor_fieldType;
          {
            RAST._IExpr _2094_onExpr;
            DCOMP._IOwnership _2095_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2096_recIdents;
            RAST._IExpr _out550;
            DCOMP._IOwnership _out551;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out552;
            (this).GenExpr(_2091_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out550, out _out551, out _out552);
            _2094_onExpr = _out550;
            _2095_onOwnership = _out551;
            _2096_recIdents = _out552;
            Dafny.ISequence<Dafny.Rune> _2097_selName;
            _2097_selName = Std.Strings.__default.OfNat(_2092_idx);
            DAST._IType _source102 = _2093_fieldType;
            {
              if (_source102.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2098_tps = _source102.dtor_Tuple_a0;
                if (((_2093_fieldType).is_Tuple) && ((new BigInteger((_2098_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _2097_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2097_selName);
                }
                goto after_match47;
              }
            }
            {
            }
          after_match47: ;
            r = ((_2094_onExpr).Sel(_2097_selName)).Clone();
            RAST._IExpr _out553;
            DCOMP._IOwnership _out554;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out553, out _out554);
            r = _out553;
            resultingOwnership = _out554;
            readIdents = _2096_recIdents;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_Call) {
          DAST._IExpression _2099_on = _source97.dtor_on;
          DAST._ICallName _2100_name = _source97.dtor_callName;
          Dafny.ISequence<DAST._IType> _2101_typeArgs = _source97.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2102_args = _source97.dtor_args;
          {
            Dafny.ISequence<RAST._IExpr> _2103_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2104_recIdents;
            Dafny.ISequence<RAST._IType> _2105_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _2106_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out555;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out556;
            Dafny.ISequence<RAST._IType> _out557;
            Std.Wrappers._IOption<DAST._IResolvedType> _out558;
            (this).GenArgs(selfIdent, _2100_name, _2101_typeArgs, _2102_args, env, out _out555, out _out556, out _out557, out _out558);
            _2103_argExprs = _out555;
            _2104_recIdents = _out556;
            _2105_typeExprs = _out557;
            _2106_fullNameQualifier = _out558;
            readIdents = _2104_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source103 = _2106_fullNameQualifier;
            {
              if (_source103.is_Some) {
                DAST._IResolvedType value11 = _source103.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2107_path = value11.dtor_path;
                Dafny.ISequence<DAST._IType> _2108_onTypeArgs = value11.dtor_typeArgs;
                DAST._IResolvedTypeBase _2109_base = value11.dtor_kind;
                RAST._IExpr _2110_fullPath;
                RAST._IExpr _out559;
                _out559 = DCOMP.COMP.GenPathExpr(_2107_path);
                _2110_fullPath = _out559;
                Dafny.ISequence<RAST._IType> _2111_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out560;
                _out560 = (this).GenTypeArgs(_2108_onTypeArgs, DCOMP.GenTypeContext.@default());
                _2111_onTypeExprs = _out560;
                RAST._IExpr _2112_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _2113_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2114_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_2109_base).is_Trait) || ((_2109_base).is_Class)) {
                  RAST._IExpr _out561;
                  DCOMP._IOwnership _out562;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out563;
                  (this).GenExpr(_2099_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out561, out _out562, out _out563);
                  _2112_onExpr = _out561;
                  _2113_recOwnership = _out562;
                  _2114_recIdents = _out563;
                  _2112_onExpr = ((this).read__macro).Apply1(_2112_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2114_recIdents);
                } else {
                  RAST._IExpr _out564;
                  DCOMP._IOwnership _out565;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out566;
                  (this).GenExpr(_2099_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out564, out _out565, out _out566);
                  _2112_onExpr = _out564;
                  _2113_recOwnership = _out565;
                  _2114_recIdents = _out566;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2114_recIdents);
                }
                r = ((((_2110_fullPath).ApplyType(_2111_onTypeExprs)).MSel(DCOMP.__default.escapeName((_2100_name).dtor_name))).ApplyType(_2105_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_2112_onExpr), _2103_argExprs));
                RAST._IExpr _out567;
                DCOMP._IOwnership _out568;
                (this).FromOwned(r, expectedOwnership, out _out567, out _out568);
                r = _out567;
                resultingOwnership = _out568;
                goto after_match48;
              }
            }
            {
              RAST._IExpr _2115_onExpr;
              DCOMP._IOwnership _2116___v199;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2117_recIdents;
              RAST._IExpr _out569;
              DCOMP._IOwnership _out570;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out571;
              (this).GenExpr(_2099_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out569, out _out570, out _out571);
              _2115_onExpr = _out569;
              _2116___v199 = _out570;
              _2117_recIdents = _out571;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2117_recIdents);
              Dafny.ISequence<Dafny.Rune> _2118_renderedName;
              DAST._ICallName _source104 = _2100_name;
              {
                if (_source104.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _2119_ident = _source104.dtor_name;
                  _2118_renderedName = DCOMP.__default.escapeName(_2119_ident);
                  goto after_match49;
                }
              }
              {
                bool disjunctiveMatch13 = false;
                if (_source104.is_MapBuilderAdd) {
                  disjunctiveMatch13 = true;
                }
                if (_source104.is_SetBuilderAdd) {
                  disjunctiveMatch13 = true;
                }
                if (disjunctiveMatch13) {
                  _2118_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                  goto after_match49;
                }
              }
              {
                _2118_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
              }
            after_match49: ;
              DAST._IExpression _source105 = _2099_on;
              {
                if (_source105.is_Companion) {
                  {
                    _2115_onExpr = (_2115_onExpr).MSel(_2118_renderedName);
                  }
                  goto after_match50;
                }
              }
              {
                {
                  if (!object.Equals(_2115_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source106 = _2100_name;
                    {
                      if (_source106.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType2 = _source106.dtor_onType;
                        if (onType2.is_Some) {
                          DAST._IType _2120_tpe = onType2.dtor_value;
                          RAST._IType _2121_typ;
                          RAST._IType _out572;
                          _out572 = (this).GenType(_2120_tpe, DCOMP.GenTypeContext.@default());
                          _2121_typ = _out572;
                          if ((_2121_typ).IsObjectOrPointer()) {
                            _2115_onExpr = ((this).read__macro).Apply1(_2115_onExpr);
                          }
                          goto after_match51;
                        }
                      }
                    }
                    {
                    }
                  after_match51: ;
                  }
                  _2115_onExpr = (_2115_onExpr).Sel(_2118_renderedName);
                }
              }
            after_match50: ;
              r = ((_2115_onExpr).ApplyType(_2105_typeExprs)).Apply(_2103_argExprs);
              RAST._IExpr _out573;
              DCOMP._IOwnership _out574;
              (this).FromOwned(r, expectedOwnership, out _out573, out _out574);
              r = _out573;
              resultingOwnership = _out574;
              return ;
            }
          after_match48: ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2122_paramsDafny = _source97.dtor_params;
          DAST._IType _2123_retType = _source97.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2124_body = _source97.dtor_body;
          {
            Dafny.ISequence<RAST._IFormal> _2125_params;
            Dafny.ISequence<RAST._IFormal> _out575;
            _out575 = (this).GenParams(_2122_paramsDafny);
            _2125_params = _out575;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2126_paramNames;
            _2126_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2127_paramTypesMap;
            _2127_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi48 = new BigInteger((_2125_params).Count);
            for (BigInteger _2128_i = BigInteger.Zero; _2128_i < _hi48; _2128_i++) {
              Dafny.ISequence<Dafny.Rune> _2129_name;
              _2129_name = ((_2125_params).Select(_2128_i)).dtor_name;
              _2126_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2126_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2129_name));
              _2127_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2127_paramTypesMap, _2129_name, ((_2125_params).Select(_2128_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _2130_subEnv;
            _2130_subEnv = ((env).ToOwned()).merge(DCOMP.Environment.create(_2126_paramNames, _2127_paramTypesMap));
            RAST._IExpr _2131_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2132_recIdents;
            DCOMP._IEnvironment _2133___v210;
            RAST._IExpr _out576;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out577;
            DCOMP._IEnvironment _out578;
            (this).GenStmts(_2124_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _2130_subEnv, true, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out576, out _out577, out _out578);
            _2131_recursiveGen = _out576;
            _2132_recIdents = _out577;
            _2133___v210 = _out578;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _2132_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2132_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_2134_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll7 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_7 in (_2134_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _2135_name = (Dafny.ISequence<Dafny.Rune>)_compr_7;
                if ((_2134_paramNames).Contains(_2135_name)) {
                  _coll7.Add(_2135_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll7);
            }))())(_2126_paramNames));
            RAST._IExpr _2136_allReadCloned;
            _2136_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_2132_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _2137_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_2132_recIdents).Elements) {
                _2137_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_2132_recIdents).Contains(_2137_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 4908)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_2137_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _2138_selfCloned;
                DCOMP._IOwnership _2139___v211;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2140___v212;
                RAST._IExpr _out579;
                DCOMP._IOwnership _out580;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out581;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out579, out _out580, out _out581);
                _2138_selfCloned = _out579;
                _2139___v211 = _out580;
                _2140___v212 = _out581;
                _2136_allReadCloned = (_2136_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2138_selfCloned)));
              } else if (!((_2126_paramNames).Contains(_2137_next))) {
                RAST._IExpr _2141_copy;
                _2141_copy = (RAST.Expr.create_Identifier(_2137_next)).Clone();
                _2136_allReadCloned = (_2136_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2137_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2141_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2137_next));
              }
              _2132_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2132_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2137_next));
            }
            RAST._IType _2142_retTypeGen;
            RAST._IType _out582;
            _out582 = (this).GenType(_2123_retType, DCOMP.GenTypeContext.InFn());
            _2142_retTypeGen = _out582;
            r = RAST.Expr.create_Block((_2136_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_2125_params, Std.Wrappers.Option<RAST._IType>.create_Some(_2142_retTypeGen), RAST.Expr.create_Block(_2131_recursiveGen)))));
            RAST._IExpr _out583;
            DCOMP._IOwnership _out584;
            (this).FromOwned(r, expectedOwnership, out _out583, out _out584);
            r = _out583;
            resultingOwnership = _out584;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2143_values = _source97.dtor_values;
          DAST._IType _2144_retType = _source97.dtor_retType;
          DAST._IExpression _2145_expr = _source97.dtor_expr;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2146_paramNames;
            _2146_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2147_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out585;
            _out585 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2148_value) => {
              return (_2148_value).dtor__0;
            })), _2143_values));
            _2147_paramFormals = _out585;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2149_paramTypes;
            _2149_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2150_paramNamesSet;
            _2150_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi49 = new BigInteger((_2143_values).Count);
            for (BigInteger _2151_i = BigInteger.Zero; _2151_i < _hi49; _2151_i++) {
              Dafny.ISequence<Dafny.Rune> _2152_name;
              _2152_name = (((_2143_values).Select(_2151_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2153_rName;
              _2153_rName = DCOMP.__default.escapeName(_2152_name);
              _2146_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2146_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2153_rName));
              _2149_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2149_paramTypes, _2153_rName, ((_2147_paramFormals).Select(_2151_i)).dtor_tpe);
              _2150_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2150_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2153_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi50 = new BigInteger((_2143_values).Count);
            for (BigInteger _2154_i = BigInteger.Zero; _2154_i < _hi50; _2154_i++) {
              RAST._IType _2155_typeGen;
              RAST._IType _out586;
              _out586 = (this).GenType((((_2143_values).Select(_2154_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.InFn());
              _2155_typeGen = _out586;
              RAST._IExpr _2156_valueGen;
              DCOMP._IOwnership _2157___v213;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2158_recIdents;
              RAST._IExpr _out587;
              DCOMP._IOwnership _out588;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out589;
              (this).GenExpr(((_2143_values).Select(_2154_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out587, out _out588, out _out589);
              _2156_valueGen = _out587;
              _2157___v213 = _out588;
              _2158_recIdents = _out589;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_2143_values).Select(_2154_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2155_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2156_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2158_recIdents);
            }
            DCOMP._IEnvironment _2159_newEnv;
            _2159_newEnv = DCOMP.Environment.create(_2146_paramNames, _2149_paramTypes);
            RAST._IExpr _2160_recGen;
            DCOMP._IOwnership _2161_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2162_recIdents;
            RAST._IExpr _out590;
            DCOMP._IOwnership _out591;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out592;
            (this).GenExpr(_2145_expr, selfIdent, _2159_newEnv, expectedOwnership, out _out590, out _out591, out _out592);
            _2160_recGen = _out590;
            _2161_recOwned = _out591;
            _2162_recIdents = _out592;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2162_recIdents, _2150_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2160_recGen));
            RAST._IExpr _out593;
            DCOMP._IOwnership _out594;
            (this).FromOwnership(r, _2161_recOwned, expectedOwnership, out _out593, out _out594);
            r = _out593;
            resultingOwnership = _out594;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2163_name = _source97.dtor_ident;
          DAST._IType _2164_tpe = _source97.dtor_typ;
          DAST._IExpression _2165_value = _source97.dtor_value;
          DAST._IExpression _2166_iifeBody = _source97.dtor_iifeBody;
          {
            RAST._IExpr _2167_valueGen;
            DCOMP._IOwnership _2168___v214;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2169_recIdents;
            RAST._IExpr _out595;
            DCOMP._IOwnership _out596;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out597;
            (this).GenExpr(_2165_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out595, out _out596, out _out597);
            _2167_valueGen = _out595;
            _2168___v214 = _out596;
            _2169_recIdents = _out597;
            readIdents = _2169_recIdents;
            RAST._IType _2170_valueTypeGen;
            RAST._IType _out598;
            _out598 = (this).GenType(_2164_tpe, DCOMP.GenTypeContext.InFn());
            _2170_valueTypeGen = _out598;
            RAST._IExpr _2171_bodyGen;
            DCOMP._IOwnership _2172___v215;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2173_bodyIdents;
            RAST._IExpr _out599;
            DCOMP._IOwnership _out600;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out601;
            (this).GenExpr(_2166_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out599, out _out600, out _out601);
            _2171_bodyGen = _out599;
            _2172___v215 = _out600;
            _2173_bodyIdents = _out601;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2173_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_2163_name)))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_2163_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_2170_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2167_valueGen))).Then(_2171_bodyGen));
            RAST._IExpr _out602;
            DCOMP._IOwnership _out603;
            (this).FromOwned(r, expectedOwnership, out _out602, out _out603);
            r = _out602;
            resultingOwnership = _out603;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_Apply) {
          DAST._IExpression _2174_func = _source97.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2175_args = _source97.dtor_args;
          {
            RAST._IExpr _2176_funcExpr;
            DCOMP._IOwnership _2177___v216;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2178_recIdents;
            RAST._IExpr _out604;
            DCOMP._IOwnership _out605;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out606;
            (this).GenExpr(_2174_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out604, out _out605, out _out606);
            _2176_funcExpr = _out604;
            _2177___v216 = _out605;
            _2178_recIdents = _out606;
            readIdents = _2178_recIdents;
            Dafny.ISequence<RAST._IExpr> _2179_rArgs;
            _2179_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi51 = new BigInteger((_2175_args).Count);
            for (BigInteger _2180_i = BigInteger.Zero; _2180_i < _hi51; _2180_i++) {
              RAST._IExpr _2181_argExpr;
              DCOMP._IOwnership _2182_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2183_argIdents;
              RAST._IExpr _out607;
              DCOMP._IOwnership _out608;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out609;
              (this).GenExpr((_2175_args).Select(_2180_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out607, out _out608, out _out609);
              _2181_argExpr = _out607;
              _2182_argOwned = _out608;
              _2183_argIdents = _out609;
              _2179_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2179_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2181_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2183_argIdents);
            }
            r = (_2176_funcExpr).Apply(_2179_rArgs);
            RAST._IExpr _out610;
            DCOMP._IOwnership _out611;
            (this).FromOwned(r, expectedOwnership, out _out610, out _out611);
            r = _out610;
            resultingOwnership = _out611;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_TypeTest) {
          DAST._IExpression _2184_on = _source97.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2185_dType = _source97.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2186_variant = _source97.dtor_variant;
          {
            RAST._IExpr _2187_exprGen;
            DCOMP._IOwnership _2188___v217;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2189_recIdents;
            RAST._IExpr _out612;
            DCOMP._IOwnership _out613;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out614;
            (this).GenExpr(_2184_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out612, out _out613, out _out614);
            _2187_exprGen = _out612;
            _2188___v217 = _out613;
            _2189_recIdents = _out614;
            RAST._IType _2190_dTypePath;
            RAST._IType _out615;
            _out615 = DCOMP.COMP.GenPath(_2185_dType);
            _2190_dTypePath = _out615;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2187_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_2190_dTypePath).MSel(DCOMP.__default.escapeName(_2186_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out616;
            DCOMP._IOwnership _out617;
            (this).FromOwned(r, expectedOwnership, out _out616, out _out617);
            r = _out616;
            resultingOwnership = _out617;
            readIdents = _2189_recIdents;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_BoolBoundedPool) {
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
          goto after_match42;
        }
      }
      {
        if (_source97.is_SetBoundedPool) {
          DAST._IExpression _2191_of = _source97.dtor_of;
          {
            RAST._IExpr _2192_exprGen;
            DCOMP._IOwnership _2193___v218;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2194_recIdents;
            RAST._IExpr _out620;
            DCOMP._IOwnership _out621;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
            (this).GenExpr(_2191_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out620, out _out621, out _out622);
            _2192_exprGen = _out620;
            _2193___v218 = _out621;
            _2194_recIdents = _out622;
            r = ((_2192_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out623;
            DCOMP._IOwnership _out624;
            (this).FromOwned(r, expectedOwnership, out _out623, out _out624);
            r = _out623;
            resultingOwnership = _out624;
            readIdents = _2194_recIdents;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_SeqBoundedPool) {
          DAST._IExpression _2195_of = _source97.dtor_of;
          bool _2196_includeDuplicates = _source97.dtor_includeDuplicates;
          {
            RAST._IExpr _2197_exprGen;
            DCOMP._IOwnership _2198___v219;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2199_recIdents;
            RAST._IExpr _out625;
            DCOMP._IOwnership _out626;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out627;
            (this).GenExpr(_2195_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out625, out _out626, out _out627);
            _2197_exprGen = _out625;
            _2198___v219 = _out626;
            _2199_recIdents = _out627;
            r = ((_2197_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2196_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out628;
            DCOMP._IOwnership _out629;
            (this).FromOwned(r, expectedOwnership, out _out628, out _out629);
            r = _out628;
            resultingOwnership = _out629;
            readIdents = _2199_recIdents;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_MapBoundedPool) {
          DAST._IExpression _2200_of = _source97.dtor_of;
          {
            RAST._IExpr _2201_exprGen;
            DCOMP._IOwnership _2202___v220;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2203_recIdents;
            RAST._IExpr _out630;
            DCOMP._IOwnership _out631;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out632;
            (this).GenExpr(_2200_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out630, out _out631, out _out632);
            _2201_exprGen = _out630;
            _2202___v220 = _out631;
            _2203_recIdents = _out632;
            r = ((((_2201_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2203_recIdents;
            RAST._IExpr _out633;
            DCOMP._IOwnership _out634;
            (this).FromOwned(r, expectedOwnership, out _out633, out _out634);
            r = _out633;
            resultingOwnership = _out634;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_IntRange) {
          DAST._IExpression _2204_lo = _source97.dtor_lo;
          DAST._IExpression _2205_hi = _source97.dtor_hi;
          bool _2206_up = _source97.dtor_up;
          {
            RAST._IExpr _2207_lo;
            DCOMP._IOwnership _2208___v221;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2209_recIdentsLo;
            RAST._IExpr _out635;
            DCOMP._IOwnership _out636;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out637;
            (this).GenExpr(_2204_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out635, out _out636, out _out637);
            _2207_lo = _out635;
            _2208___v221 = _out636;
            _2209_recIdentsLo = _out637;
            RAST._IExpr _2210_hi;
            DCOMP._IOwnership _2211___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2212_recIdentsHi;
            RAST._IExpr _out638;
            DCOMP._IOwnership _out639;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out640;
            (this).GenExpr(_2205_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out638, out _out639, out _out640);
            _2210_hi = _out638;
            _2211___v222 = _out639;
            _2212_recIdentsHi = _out640;
            if (_2206_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2207_lo, _2210_hi));
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2210_hi, _2207_lo));
            }
            RAST._IExpr _out641;
            DCOMP._IOwnership _out642;
            (this).FromOwned(r, expectedOwnership, out _out641, out _out642);
            r = _out641;
            resultingOwnership = _out642;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2209_recIdentsLo, _2212_recIdentsHi);
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_UnboundedIntRange) {
          DAST._IExpression _2213_start = _source97.dtor_start;
          bool _2214_up = _source97.dtor_up;
          {
            RAST._IExpr _2215_start;
            DCOMP._IOwnership _2216___v223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2217_recIdentStart;
            RAST._IExpr _out643;
            DCOMP._IOwnership _out644;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out645;
            (this).GenExpr(_2213_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out643, out _out644, out _out645);
            _2215_start = _out643;
            _2216___v223 = _out644;
            _2217_recIdentStart = _out645;
            if (_2214_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).Apply1(_2215_start);
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).Apply1(_2215_start);
            }
            RAST._IExpr _out646;
            DCOMP._IOwnership _out647;
            (this).FromOwned(r, expectedOwnership, out _out646, out _out647);
            r = _out646;
            resultingOwnership = _out647;
            readIdents = _2217_recIdentStart;
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_MapBuilder) {
          DAST._IType _2218_keyType = _source97.dtor_keyType;
          DAST._IType _2219_valueType = _source97.dtor_valueType;
          {
            RAST._IType _2220_kType;
            RAST._IType _out648;
            _out648 = (this).GenType(_2218_keyType, DCOMP.GenTypeContext.@default());
            _2220_kType = _out648;
            RAST._IType _2221_vType;
            RAST._IType _out649;
            _out649 = (this).GenType(_2219_valueType, DCOMP.GenTypeContext.@default());
            _2221_vType = _out649;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2220_kType, _2221_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out650;
            DCOMP._IOwnership _out651;
            (this).FromOwned(r, expectedOwnership, out _out650, out _out651);
            r = _out650;
            resultingOwnership = _out651;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match42;
        }
      }
      {
        if (_source97.is_SetBuilder) {
          DAST._IType _2222_elemType = _source97.dtor_elemType;
          {
            RAST._IType _2223_eType;
            RAST._IType _out652;
            _out652 = (this).GenType(_2222_elemType, DCOMP.GenTypeContext.@default());
            _2223_eType = _out652;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2223_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out653;
            DCOMP._IOwnership _out654;
            (this).FromOwned(r, expectedOwnership, out _out653, out _out654);
            r = _out653;
            resultingOwnership = _out654;
            return ;
          }
          goto after_match42;
        }
      }
      {
        DAST._IType _2224_elemType = _source97.dtor_elemType;
        DAST._IExpression _2225_collection = _source97.dtor_collection;
        bool _2226_is__forall = _source97.dtor_is__forall;
        DAST._IExpression _2227_lambda = _source97.dtor_lambda;
        {
          RAST._IType _2228_tpe;
          RAST._IType _out655;
          _out655 = (this).GenType(_2224_elemType, DCOMP.GenTypeContext.@default());
          _2228_tpe = _out655;
          RAST._IExpr _2229_collectionGen;
          DCOMP._IOwnership _2230___v224;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2231_recIdents;
          RAST._IExpr _out656;
          DCOMP._IOwnership _out657;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out658;
          (this).GenExpr(_2225_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out656, out _out657, out _out658);
          _2229_collectionGen = _out656;
          _2230___v224 = _out657;
          _2231_recIdents = _out658;
          Dafny.ISequence<DAST._IAttribute> _2232_extraAttributes;
          _2232_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2225_collection).is_IntRange) || ((_2225_collection).is_UnboundedIntRange)) || ((_2225_collection).is_SeqBoundedPool)) {
            _2232_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2227_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2233_formals;
            _2233_formals = (_2227_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2234_newFormals;
            _2234_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi52 = new BigInteger((_2233_formals).Count);
            for (BigInteger _2235_i = BigInteger.Zero; _2235_i < _hi52; _2235_i++) {
              var _pat_let_tv4 = _2232_extraAttributes;
              var _pat_let_tv5 = _2233_formals;
              _2234_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2234_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2233_formals).Select(_2235_i), _pat_let34_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let34_0, _2236_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv4, ((_pat_let_tv5).Select(_2235_i)).dtor_attributes), _pat_let35_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let35_0, _2237_dt__update_hattributes_h0 => DAST.Formal.create((_2236_dt__update__tmp_h0).dtor_name, (_2236_dt__update__tmp_h0).dtor_typ, _2237_dt__update_hattributes_h0)))))));
            }
            DAST._IExpression _2238_newLambda;
            DAST._IExpression _2239_dt__update__tmp_h1 = _2227_lambda;
            Dafny.ISequence<DAST._IFormal> _2240_dt__update_hparams_h0 = _2234_newFormals;
            _2238_newLambda = DAST.Expression.create_Lambda(_2240_dt__update_hparams_h0, (_2239_dt__update__tmp_h1).dtor_retType, (_2239_dt__update__tmp_h1).dtor_body);
            RAST._IExpr _2241_lambdaGen;
            DCOMP._IOwnership _2242___v225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2243_recLambdaIdents;
            RAST._IExpr _out659;
            DCOMP._IOwnership _out660;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out661;
            (this).GenExpr(_2238_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out659, out _out660, out _out661);
            _2241_lambdaGen = _out659;
            _2242___v225 = _out660;
            _2243_recLambdaIdents = _out661;
            Dafny.ISequence<Dafny.Rune> _2244_fn;
            if (_2226_is__forall) {
              _2244_fn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all");
            } else {
              _2244_fn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any");
            }
            r = ((_2229_collectionGen).Sel(_2244_fn)).Apply1(((_2241_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2231_recIdents, _2243_recLambdaIdents);
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
    after_match42: ;
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      BigInteger _2245_i;
      _2245_i = BigInteger.Zero;
      while ((_2245_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _2246_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _2247_m;
        RAST._IMod _out664;
        _out664 = (this).GenModule((p).Select(_2245_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2247_m = _out664;
        _2246_generated = (_2247_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_2245_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2246_generated);
        _2245_i = (_2245_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2248_i;
      _2248_i = BigInteger.Zero;
      while ((_2248_i) < (new BigInteger((fullName).Count))) {
        if ((_2248_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2248_i)));
        _2248_i = (_2248_i) + (BigInteger.One);
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