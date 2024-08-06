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
            Dafny.ISequence<Dafny.Rune> _in0 = (i).Drop(new BigInteger(2));
            i = _in0;
            goto TAIL_CALL_START;
          }
        } else {
          return true;
        }
      } else {
        Dafny.ISequence<Dafny.Rune> _in1 = (i).Drop(BigInteger.One);
        i = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> idiomatic__rust(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _0___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in0 = (i).Drop(new BigInteger(2));
        i = _in0;
        goto TAIL_CALL_START;
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in1 = (i).Drop(BigInteger.One);
        i = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _0___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in0 = (i).Drop(BigInteger.One);
        i = _in0;
        goto TAIL_CALL_START;
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in1 = (i).Drop(BigInteger.One);
        i = _in1;
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
        Dafny.ISequence<Dafny.Rune> _0_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _0_r);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeField(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _0_r = (f);
      if ((DCOMP.__default.reserved__fields).Contains(_0_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _0_r);
      } else {
        return DCOMP.__default.escapeName(f);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeDtor(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _0_r = (f);
      if ((DCOMP.__default.reserved__fields).Contains(_0_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_0_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": r#_")), _0_r);
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
        Std.Wrappers._IOption<DAST._IResolvedType> _0_res = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
          DAST._IType _source0 = (rs).Select(BigInteger.Zero);
          {
            if (_source0.is_UserDefined) {
              DAST._IResolvedType _1_resolvedType = _source0.dtor_resolved;
              return DCOMP.__default.TraitTypeContainingMethod(_1_resolvedType, dafnyName);
            }
          }
          {
            return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
          }
        }))();
        Std.Wrappers._IOption<DAST._IResolvedType> _source1 = _0_res;
        {
          if (_source1.is_Some) {
            return _0_res;
          }
        }
        {
          return DCOMP.__default.TraitTypeContainingMethodAux((rs).Drop(BigInteger.One), dafnyName);
        }
      }
    }
    public static Std.Wrappers._IOption<DAST._IResolvedType> TraitTypeContainingMethod(DAST._IResolvedType r, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DAST._IResolvedType _let_tmp_rhs0 = r;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _0_path = _let_tmp_rhs0.dtor_path;
      Dafny.ISequence<DAST._IType> _1_typeArgs = _let_tmp_rhs0.dtor_typeArgs;
      DAST._IResolvedTypeBase _2_kind = _let_tmp_rhs0.dtor_kind;
      Dafny.ISequence<DAST._IAttribute> _3_attributes = _let_tmp_rhs0.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4_properMethods = _let_tmp_rhs0.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _5_extendedTypes = _let_tmp_rhs0.dtor_extendedTypes;
      if ((_4_properMethods).Contains(dafnyName)) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(r);
      } else {
        return DCOMP.__default.TraitTypeContainingMethodAux(_5_extendedTypes, dafnyName);
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
      DCOMP._IEnvironment _0_dt__update__tmp_h0 = this;
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1_dt__update_htypes_h0 = ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType>>)(() => {
        var _coll0 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_0 in ((this).dtor_types).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _2_k = (Dafny.ISequence<Dafny.Rune>)_compr_0;
          if (((this).dtor_types).Contains(_2_k)) {
            _coll0.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>(_2_k, (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,_2_k)).ToOwned()));
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IType>.FromCollection(_coll0);
      }))();
      return DCOMP.Environment.create((_0_dt__update__tmp_h0).dtor_names, _1_dt__update_htypes_h0);
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
      BigInteger _0_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _0_indexInEnv), ((this).dtor_names).Drop((_0_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
      Dafny.ISequence<Dafny.Rune> _0_modName;
      _0_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_0_modName);
      } else {
        Dafny.ISequence<RAST._IModDecl> _1_body;
        Dafny.ISequence<RAST._IModDecl> _out0;
        _out0 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _1_body = _out0;
        s = RAST.Mod.create_Mod(_0_modName, _1_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi0 = new BigInteger((body).Count);
      for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
        Dafny.ISequence<RAST._IModDecl> _1_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source0 = (body).Select(_0_i);
        {
          if (_source0.is_Module) {
            DAST._IModule _2_m = _source0.dtor_Module_a0;
            RAST._IMod _3_mm;
            RAST._IMod _out0;
            _out0 = (this).GenModule(_2_m, containingPath);
            _3_mm = _out0;
            _1_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_3_mm));
            goto after_match0;
          }
        }
        {
          if (_source0.is_Class) {
            DAST._IClass _4_c = _source0.dtor_Class_a0;
            Dafny.ISequence<RAST._IModDecl> _out1;
            _out1 = (this).GenClass(_4_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_4_c).dtor_name)));
            _1_generated = _out1;
            goto after_match0;
          }
        }
        {
          if (_source0.is_Trait) {
            DAST._ITrait _5_t = _source0.dtor_Trait_a0;
            Dafny.ISequence<RAST._IModDecl> _out2;
            _out2 = (this).GenTrait(_5_t, containingPath);
            _1_generated = _out2;
            goto after_match0;
          }
        }
        {
          if (_source0.is_Newtype) {
            DAST._INewtype _6_n = _source0.dtor_Newtype_a0;
            Dafny.ISequence<RAST._IModDecl> _out3;
            _out3 = (this).GenNewtype(_6_n);
            _1_generated = _out3;
            goto after_match0;
          }
        }
        {
          if (_source0.is_SynonymType) {
            DAST._ISynonymType _7_s = _source0.dtor_SynonymType_a0;
            Dafny.ISequence<RAST._IModDecl> _out4;
            _out4 = (this).GenSynonymType(_7_s);
            _1_generated = _out4;
            goto after_match0;
          }
        }
        {
          DAST._IDatatype _8_d = _source0.dtor_Datatype_a0;
          Dafny.ISequence<RAST._IModDecl> _out5;
          _out5 = (this).GenDatatype(_8_d);
          _1_generated = _out5;
        }
      after_match0: ;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _0_genTpConstraint;
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) {
        _0_genTpConstraint = Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq);
      } else {
        _0_genTpConstraint = Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType);
      }
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _0_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_0_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _0_genTpConstraint);
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
        BigInteger _hi0 = new BigInteger((@params).Count);
        for (BigInteger _0_tpI = BigInteger.Zero; _0_tpI < _hi0; _0_tpI++) {
          DAST._ITypeArgDecl _1_tp;
          _1_tp = (@params).Select(_0_tpI);
          DAST._IType _2_typeArg;
          RAST._ITypeParamDecl _3_typeParam;
          DAST._IType _out0;
          RAST._ITypeParamDecl _out1;
          (this).GenTypeParam(_1_tp, out _out0, out _out1);
          _2_typeArg = _out0;
          _3_typeParam = _out1;
          RAST._IType _4_rType;
          RAST._IType _out2;
          _out2 = (this).GenType(_2_typeArg, DCOMP.GenTypeContext.@default());
          _4_rType = _out2;
          typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_2_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_4_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_3_typeParam));
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
      Dafny.ISequence<DAST._IType> _0_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _3_whereConstraints;
      Dafny.ISequence<DAST._IType> _out0;
      Dafny.ISequence<RAST._IType> _out1;
      Dafny.ISequence<RAST._ITypeParamDecl> _out2;
      Dafny.ISequence<Dafny.Rune> _out3;
      (this).GenTypeParameters((c).dtor_typeParams, out _out0, out _out1, out _out2, out _out3);
      _0_typeParamsSeq = _out0;
      _1_rTypeParams = _out1;
      _2_rTypeParamsDecls = _out2;
      _3_whereConstraints = _out3;
      Dafny.ISequence<Dafny.Rune> _4_constrainedTypeParams;
      _4_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_2_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _5_fields;
      _5_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _6_fieldInits;
      _6_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi0 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _7_fieldI = BigInteger.Zero; _7_fieldI < _hi0; _7_fieldI++) {
        DAST._IField _8_field;
        _8_field = ((c).dtor_fields).Select(_7_fieldI);
        RAST._IType _9_fieldType;
        RAST._IType _out4;
        _out4 = (this).GenType(((_8_field).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
        _9_fieldType = _out4;
        Dafny.ISequence<Dafny.Rune> _10_fieldRustName;
        _10_fieldRustName = DCOMP.__default.escapeName(((_8_field).dtor_formal).dtor_name);
        _5_fields = Dafny.Sequence<RAST._IField>.Concat(_5_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_10_fieldRustName, _9_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source0 = (_8_field).dtor_defaultValue;
        {
          if (_source0.is_Some) {
            DAST._IExpression _11_e = _source0.dtor_value;
            {
              RAST._IExpr _12_expr;
              DCOMP._IOwnership _13___v48;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _14___v49;
              RAST._IExpr _out5;
              DCOMP._IOwnership _out6;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out7;
              (this).GenExpr(_11_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out5, out _out6, out _out7);
              _12_expr = _out5;
              _13___v48 = _out6;
              _14___v49 = _out7;
              _6_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_6_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_10_fieldRustName, _12_expr)));
            }
            goto after_match0;
          }
        }
        {
          {
            RAST._IExpr _15_default;
            _15_default = RAST.__default.std__Default__default;
            if ((_9_fieldType).IsObjectOrPointer()) {
              _15_default = (_9_fieldType).ToNullExpr();
            }
            _6_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_6_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_10_fieldRustName, _15_default)));
          }
        }
      after_match0: ;
      }
      BigInteger _hi1 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _16_typeParamI = BigInteger.Zero; _16_typeParamI < _hi1; _16_typeParamI++) {
        DAST._IType _17_typeArg;
        RAST._ITypeParamDecl _18_typeParam;
        DAST._IType _out8;
        RAST._ITypeParamDecl _out9;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_16_typeParamI), out _out8, out _out9);
        _17_typeArg = _out8;
        _18_typeParam = _out9;
        RAST._IType _19_rTypeArg;
        RAST._IType _out10;
        _out10 = (this).GenType(_17_typeArg, DCOMP.GenTypeContext.@default());
        _19_rTypeArg = _out10;
        _5_fields = Dafny.Sequence<RAST._IField>.Concat(_5_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_16_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_19_rTypeArg))))));
        _6_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_6_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_16_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      Dafny.ISequence<Dafny.Rune> _20_datatypeName;
      _20_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IStruct _21_struct;
      _21_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _20_datatypeName, _2_rTypeParamsDecls, RAST.Fields.create_NamedFields(_5_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_21_struct));
      Dafny.ISequence<RAST._IImplMember> _22_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _23_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out11;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out12;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(path, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Class(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _0_typeParamsSeq, out _out11, out _out12);
      _22_implBodyRaw = _out11;
      _23_traitBodies = _out12;
      Dafny.ISequence<RAST._IImplMember> _24_implBody;
      _24_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.Type.create_SelfOwned())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel((this).allocate)).ApplyType1(RAST.Type.create_SelfOwned())).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))))), _22_implBodyRaw);
      RAST._IImpl _25_i;
      _25_i = RAST.Impl.create_Impl(_2_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_20_datatypeName), _1_rTypeParams), _3_whereConstraints, _24_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_25_i)));
      RAST._IType _26_genSelfPath;
      RAST._IType _out13;
      _out13 = DCOMP.COMP.GenPath(path);
      _26_genSelfPath = _out13;
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"))))), RAST.Type.create_TypeApp(_26_genSelfPath, _1_rTypeParams), _3_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any")))))))))));
      BigInteger _hi2 = new BigInteger(((c).dtor_superClasses).Count);
      for (BigInteger _27_i = BigInteger.Zero; _27_i < _hi2; _27_i++) {
        DAST._IType _28_superClass;
        _28_superClass = ((c).dtor_superClasses).Select(_27_i);
        DAST._IType _source1 = _28_superClass;
        {
          if (_source1.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source1.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _29_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _30_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
              {
                RAST._IType _31_pathStr;
                RAST._IType _out14;
                _out14 = DCOMP.COMP.GenPath(_29_traitPath);
                _31_pathStr = _out14;
                Dafny.ISequence<RAST._IType> _32_typeArgs;
                Dafny.ISequence<RAST._IType> _out15;
                _out15 = (this).GenTypeArgs(_30_typeArgs, DCOMP.GenTypeContext.@default());
                _32_typeArgs = _out15;
                Dafny.ISequence<RAST._IImplMember> _33_body;
                _33_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_23_traitBodies).Contains(_29_traitPath)) {
                  _33_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_23_traitBodies,_29_traitPath);
                }
                RAST._IType _34_traitType;
                _34_traitType = RAST.Type.create_TypeApp(_31_pathStr, _32_typeArgs);
                RAST._IModDecl _35_x;
                _35_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, _34_traitType, RAST.Type.create_TypeApp(_26_genSelfPath, _1_rTypeParams), _3_whereConstraints, _33_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_35_x));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_34_traitType))), RAST.Type.create_TypeApp(_26_genSelfPath, _1_rTypeParams), _3_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(_34_traitType)))))))));
              }
              goto after_match1;
            }
          }
        }
        {
        }
      after_match1: ;
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _0_typeParamsSeq;
      _0_typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1_typeParamDecls;
      _1_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _2_typeParams;
      _2_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _hi0 = new BigInteger(((t).dtor_typeParams).Count);
        for (BigInteger _3_tpI = BigInteger.Zero; _3_tpI < _hi0; _3_tpI++) {
          DAST._ITypeArgDecl _4_tp;
          _4_tp = ((t).dtor_typeParams).Select(_3_tpI);
          DAST._IType _5_typeArg;
          RAST._ITypeParamDecl _6_typeParamDecl;
          DAST._IType _out0;
          RAST._ITypeParamDecl _out1;
          (this).GenTypeParam(_4_tp, out _out0, out _out1);
          _5_typeArg = _out0;
          _6_typeParamDecl = _out1;
          _0_typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(_0_typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_5_typeArg));
          _1_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_6_typeParamDecl));
          RAST._IType _7_typeParam;
          RAST._IType _out2;
          _out2 = (this).GenType(_5_typeArg, DCOMP.GenTypeContext.@default());
          _7_typeParam = _out2;
          _2_typeParams = Dafny.Sequence<RAST._IType>.Concat(_2_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_7_typeParam));
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _8_fullPath;
      _8_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _9_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _10___v54;
      Dafny.ISequence<RAST._IImplMember> _out3;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out4;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_8_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Trait(), (t).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _0_typeParamsSeq, out _out3, out _out4);
      _9_implBody = _out3;
      _10___v54 = _out4;
      Dafny.ISequence<RAST._IType> _11_parents;
      _11_parents = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi1 = new BigInteger(((t).dtor_parents).Count);
      for (BigInteger _12_i = BigInteger.Zero; _12_i < _hi1; _12_i++) {
        RAST._IType _13_tpe;
        RAST._IType _out5;
        _out5 = (this).GenType(((t).dtor_parents).Select(_12_i), DCOMP.GenTypeContext.ForTraitParents());
        _13_tpe = _out5;
        _11_parents = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.Concat(_11_parents, Dafny.Sequence<RAST._IType>.FromElements(_13_tpe)), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply1(RAST.Type.create_DynType(_13_tpe))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _2_typeParams), _11_parents, _9_implBody)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _0_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _3_whereConstraints;
      Dafny.ISequence<DAST._IType> _out0;
      Dafny.ISequence<RAST._IType> _out1;
      Dafny.ISequence<RAST._ITypeParamDecl> _out2;
      Dafny.ISequence<Dafny.Rune> _out3;
      (this).GenTypeParameters((c).dtor_typeParams, out _out0, out _out1, out _out2, out _out3);
      _0_typeParamsSeq = _out0;
      _1_rTypeParams = _out1;
      _2_rTypeParamsDecls = _out2;
      _3_whereConstraints = _out3;
      Dafny.ISequence<Dafny.Rune> _4_constrainedTypeParams;
      _4_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_2_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _5_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source0 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      {
        if (_source0.is_Some) {
          RAST._IType _6_v = _source0.dtor_value;
          _5_underlyingType = _6_v;
          goto after_match0;
        }
      }
      {
        RAST._IType _out4;
        _out4 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
        _5_underlyingType = _out4;
      }
    after_match0: ;
      DAST._IType _7_resultingType;
      _7_resultingType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _8_newtypeName;
      _8_newtypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _8_newtypeName, _2_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _5_underlyingType))))));
      RAST._IExpr _9_fnBody;
      _9_fnBody = RAST.Expr.create_Identifier(_8_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source1 = (c).dtor_witnessExpr;
      {
        if (_source1.is_Some) {
          DAST._IExpression _10_e = _source1.dtor_value;
          {
            DAST._IExpression _11_e;
            if (object.Equals((c).dtor_base, _7_resultingType)) {
              _11_e = _10_e;
            } else {
              _11_e = DAST.Expression.create_Convert(_10_e, (c).dtor_base, _7_resultingType);
            }
            RAST._IExpr _12_eStr;
            DCOMP._IOwnership _13___v55;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _14___v56;
            RAST._IExpr _out5;
            DCOMP._IOwnership _out6;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out7;
            (this).GenExpr(_11_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out5, out _out6, out _out7);
            _12_eStr = _out5;
            _13___v55 = _out6;
            _14___v56 = _out7;
            _9_fnBody = (_9_fnBody).Apply1(_12_eStr);
          }
          goto after_match1;
        }
      }
      {
        {
          _9_fnBody = (_9_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
    after_match1: ;
      RAST._IImplMember _15_body;
      _15_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_9_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source2 = (c).dtor_constraint;
      {
        if (_source2.is_None) {
          goto after_match2;
        }
      }
      {
        DAST._INewtypeConstraint value0 = _source2.dtor_value;
        DAST._IFormal _16_formal = value0.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _17_constraintStmts = value0.dtor_constraintStmts;
        RAST._IExpr _18_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _19___v57;
        DCOMP._IEnvironment _20_newEnv;
        RAST._IExpr _out8;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out9;
        DCOMP._IEnvironment _out10;
        (this).GenStmts(_17_constraintStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out8, out _out9, out _out10);
        _18_rStmts = _out8;
        _19___v57 = _out9;
        _20_newEnv = _out10;
        Dafny.ISequence<RAST._IFormal> _21_rFormals;
        Dafny.ISequence<RAST._IFormal> _out11;
        _out11 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_16_formal));
        _21_rFormals = _out11;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_2_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_8_newtypeName), _1_rTypeParams), _3_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _21_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_18_rStmts))))))));
      }
    after_match2: ;
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_8_newtypeName), _1_rTypeParams), _3_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_15_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_8_newtypeName), _1_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_8_newtypeName), _1_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_5_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _0_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _3_whereConstraints;
      Dafny.ISequence<DAST._IType> _out0;
      Dafny.ISequence<RAST._IType> _out1;
      Dafny.ISequence<RAST._ITypeParamDecl> _out2;
      Dafny.ISequence<Dafny.Rune> _out3;
      (this).GenTypeParameters((c).dtor_typeParams, out _out0, out _out1, out _out2, out _out3);
      _0_typeParamsSeq = _out0;
      _1_rTypeParams = _out1;
      _2_rTypeParamsDecls = _out2;
      _3_whereConstraints = _out3;
      Dafny.ISequence<Dafny.Rune> _4_constrainedTypeParams;
      _4_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_2_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<Dafny.Rune> _5_synonymTypeName;
      _5_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _6_resultingType;
      RAST._IType _out4;
      _out4 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
      _6_resultingType = _out4;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _5_synonymTypeName, _2_rTypeParamsDecls, _6_resultingType)));
      Std.Wrappers._IOption<DAST._IExpression> _source0 = (c).dtor_witnessExpr;
      {
        if (_source0.is_Some) {
          DAST._IExpression _7_e = _source0.dtor_value;
          {
            RAST._IExpr _8_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _9___v58;
            DCOMP._IEnvironment _10_newEnv;
            RAST._IExpr _out5;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out6;
            DCOMP._IEnvironment _out7;
            (this).GenStmts((c).dtor_witnessStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out5, out _out6, out _out7);
            _8_rStmts = _out5;
            _9___v58 = _out6;
            _10_newEnv = _out7;
            RAST._IExpr _11_rExpr;
            DCOMP._IOwnership _12___v59;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _13___v60;
            RAST._IExpr _out8;
            DCOMP._IOwnership _out9;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out10;
            (this).GenExpr(_7_e, DCOMP.SelfInfo.create_NoSelf(), _10_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out8, out _out9, out _out10);
            _11_rExpr = _out8;
            _12___v59 = _out9;
            _13___v60 = _out10;
            Dafny.ISequence<Dafny.Rune> _14_constantName;
            _14_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_14_constantName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_6_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_8_rStmts).Then(_11_rExpr)))))));
          }
          goto after_match0;
        }
      }
      {
      }
    after_match0: ;
      return s;
    }
    public bool TypeIsEq(DAST._IType t) {
      DAST._IType _source0 = t;
      {
        if (_source0.is_UserDefined) {
          return true;
        }
      }
      {
        if (_source0.is_Tuple) {
          Dafny.ISequence<DAST._IType> _0_ts = _source0.dtor_Tuple_a0;
          return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, bool>>((_1_ts) => Dafny.Helpers.Quantifier<DAST._IType>((_1_ts).UniqueElements, true, (((_forall_var_0) => {
            DAST._IType _2_t = (DAST._IType)_forall_var_0;
            return !((_1_ts).Contains(_2_t)) || ((this).TypeIsEq(_2_t));
          }))))(_0_ts);
        }
      }
      {
        if (_source0.is_Array) {
          DAST._IType _3_t = _source0.dtor_element;
          return (this).TypeIsEq(_3_t);
        }
      }
      {
        if (_source0.is_Seq) {
          DAST._IType _4_t = _source0.dtor_element;
          return (this).TypeIsEq(_4_t);
        }
      }
      {
        if (_source0.is_Set) {
          DAST._IType _5_t = _source0.dtor_element;
          return (this).TypeIsEq(_5_t);
        }
      }
      {
        if (_source0.is_Multiset) {
          DAST._IType _6_t = _source0.dtor_element;
          return (this).TypeIsEq(_6_t);
        }
      }
      {
        if (_source0.is_Map) {
          DAST._IType _7_k = _source0.dtor_key;
          DAST._IType _8_v = _source0.dtor_value;
          return ((this).TypeIsEq(_7_k)) && ((this).TypeIsEq(_8_v));
        }
      }
      {
        if (_source0.is_SetBuilder) {
          DAST._IType _9_t = _source0.dtor_element;
          return (this).TypeIsEq(_9_t);
        }
      }
      {
        if (_source0.is_MapBuilder) {
          DAST._IType _10_k = _source0.dtor_key;
          DAST._IType _11_v = _source0.dtor_value;
          return ((this).TypeIsEq(_10_k)) && ((this).TypeIsEq(_11_v));
        }
      }
      {
        if (_source0.is_Arrow) {
          return false;
        }
      }
      {
        if (_source0.is_Primitive) {
          return true;
        }
      }
      {
        if (_source0.is_Passthrough) {
          return true;
        }
      }
      {
        if (_source0.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _12_i = _source0.dtor_TypeArg_a0;
          return true;
        }
      }
      {
        return true;
      }
    }
    public bool DatatypeIsEq(DAST._IDatatype c) {
      return (!((c).dtor_isCo)) && (Dafny.Helpers.Id<Func<DAST._IDatatype, bool>>((_0_c) => Dafny.Helpers.Quantifier<DAST._IDatatypeCtor>(((_0_c).dtor_ctors).UniqueElements, true, (((_forall_var_0) => {
        DAST._IDatatypeCtor _1_ctor = (DAST._IDatatypeCtor)_forall_var_0;
        return Dafny.Helpers.Quantifier<DAST._IDatatypeDtor>(((_1_ctor).dtor_args).UniqueElements, true, (((_forall_var_1) => {
          DAST._IDatatypeDtor _2_arg = (DAST._IDatatypeDtor)_forall_var_1;
          return !((((_0_c).dtor_ctors).Contains(_1_ctor)) && (((_1_ctor).dtor_args).Contains(_2_arg))) || ((this).TypeIsEq(((_2_arg).dtor_formal).dtor_typ));
        })));
      }))))(c));
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _0_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _3_whereConstraints;
      Dafny.ISequence<DAST._IType> _out0;
      Dafny.ISequence<RAST._IType> _out1;
      Dafny.ISequence<RAST._ITypeParamDecl> _out2;
      Dafny.ISequence<Dafny.Rune> _out3;
      (this).GenTypeParameters((c).dtor_typeParams, out _out0, out _out1, out _out2, out _out3);
      _0_typeParamsSeq = _out0;
      _1_rTypeParams = _out1;
      _2_rTypeParamsDecls = _out2;
      _3_whereConstraints = _out3;
      Dafny.ISequence<Dafny.Rune> _4_datatypeName;
      _4_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _5_ctors;
      _5_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      Dafny.ISequence<DAST._IVariance> _6_variances;
      _6_variances = Std.Collections.Seq.__default.Map<DAST._ITypeArgDecl, DAST._IVariance>(((System.Func<DAST._ITypeArgDecl, DAST._IVariance>)((_7_typeParamDecl) => {
        return (_7_typeParamDecl).dtor_variance;
      })), (c).dtor_typeParams);
      BigInteger _hi0 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _8_i = BigInteger.Zero; _8_i < _hi0; _8_i++) {
        DAST._IDatatypeCtor _9_ctor;
        _9_ctor = ((c).dtor_ctors).Select(_8_i);
        Dafny.ISequence<RAST._IField> _10_ctorArgs;
        _10_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _11_isNumeric;
        _11_isNumeric = false;
        BigInteger _hi1 = new BigInteger(((_9_ctor).dtor_args).Count);
        for (BigInteger _12_j = BigInteger.Zero; _12_j < _hi1; _12_j++) {
          DAST._IDatatypeDtor _13_dtor;
          _13_dtor = ((_9_ctor).dtor_args).Select(_12_j);
          RAST._IType _14_formalType;
          RAST._IType _out4;
          _out4 = (this).GenType(((_13_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
          _14_formalType = _out4;
          Dafny.ISequence<Dafny.Rune> _15_formalName;
          _15_formalName = DCOMP.__default.escapeName(((_13_dtor).dtor_formal).dtor_name);
          if (((_12_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_15_formalName))) {
            _11_isNumeric = true;
          }
          if ((((_12_j).Sign != 0) && (_11_isNumeric)) && (!(Std.Strings.__default.OfNat(_12_j)).Equals(_15_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _15_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_12_j)));
            _11_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _10_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_10_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_15_formalName, RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_14_formalType))))));
          } else {
            _10_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_10_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_15_formalName, _14_formalType))));
          }
        }
        RAST._IFields _16_namedFields;
        _16_namedFields = RAST.Fields.create_NamedFields(_10_ctorArgs);
        if (_11_isNumeric) {
          _16_namedFields = (_16_namedFields).ToNamelessFields();
        }
        _5_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_5_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_9_ctor).dtor_name), _16_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _17_selfPath;
      _17_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _18_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _19_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out5;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out6;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_17_selfPath, _0_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype(_6_variances), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _0_typeParamsSeq, out _out5, out _out6);
      _18_implBodyRaw = _out5;
      _19_traitBodies = _out6;
      Dafny.ISequence<RAST._IImplMember> _20_implBody;
      _20_implBody = _18_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _21_emittedFields;
      _21_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi2 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _22_i = BigInteger.Zero; _22_i < _hi2; _22_i++) {
        DAST._IDatatypeCtor _23_ctor;
        _23_ctor = ((c).dtor_ctors).Select(_22_i);
        BigInteger _hi3 = new BigInteger(((_23_ctor).dtor_args).Count);
        for (BigInteger _24_j = BigInteger.Zero; _24_j < _hi3; _24_j++) {
          DAST._IDatatypeDtor _25_dtor;
          _25_dtor = ((_23_ctor).dtor_args).Select(_24_j);
          Dafny.ISequence<Dafny.Rune> _26_callName;
          _26_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_25_dtor).dtor_callName, DCOMP.__default.escapeName(((_25_dtor).dtor_formal).dtor_name));
          if (!((_21_emittedFields).Contains(_26_callName))) {
            _21_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_21_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_26_callName));
            RAST._IType _27_formalType;
            RAST._IType _out7;
            _out7 = (this).GenType(((_25_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
            _27_formalType = _out7;
            Dafny.ISequence<RAST._IMatchCase> _28_cases;
            _28_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi4 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _29_k = BigInteger.Zero; _29_k < _hi4; _29_k++) {
              DAST._IDatatypeCtor _30_ctor2;
              _30_ctor2 = ((c).dtor_ctors).Select(_29_k);
              Dafny.ISequence<Dafny.Rune> _31_pattern;
              _31_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_30_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _32_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _33_hasMatchingField;
              _33_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _34_patternInner;
              _34_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _35_isNumeric;
              _35_isNumeric = false;
              BigInteger _hi5 = new BigInteger(((_30_ctor2).dtor_args).Count);
              for (BigInteger _36_l = BigInteger.Zero; _36_l < _hi5; _36_l++) {
                DAST._IDatatypeDtor _37_dtor2;
                _37_dtor2 = ((_30_ctor2).dtor_args).Select(_36_l);
                Dafny.ISequence<Dafny.Rune> _38_patternName;
                _38_patternName = DCOMP.__default.escapeDtor(((_37_dtor2).dtor_formal).dtor_name);
                Dafny.ISequence<Dafny.Rune> _39_varName;
                _39_varName = DCOMP.__default.escapeField(((_37_dtor2).dtor_formal).dtor_name);
                if (((_36_l).Sign == 0) && ((_38_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _35_isNumeric = true;
                }
                if (_35_isNumeric) {
                  _38_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_37_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_36_l)));
                  _39_varName = _38_patternName;
                }
                if (object.Equals(((_25_dtor).dtor_formal).dtor_name, ((_37_dtor2).dtor_formal).dtor_name)) {
                  _33_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_39_varName);
                }
                _34_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_34_patternInner, _38_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_35_isNumeric) {
                _31_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_31_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _34_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _31_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_31_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _34_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_33_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _32_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_33_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _32_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_33_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _32_rhs = (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("field does not exist on this variant"));
              }
              RAST._IMatchCase _40_ctorMatch;
              _40_ctorMatch = RAST.MatchCase.create(_31_pattern, RAST.Expr.create_RawExpr(_32_rhs));
              _28_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_28_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_40_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _28_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_28_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_4_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr((this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))))));
            }
            RAST._IExpr _41_methodBody;
            _41_methodBody = RAST.Expr.create_Match(RAST.__default.self, _28_cases);
            _20_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_20_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_26_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_27_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_41_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _42_coerceTypes;
      _42_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _43_rCoerceTypeParams;
      _43_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _44_coerceArguments;
      _44_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _45_coerceMap;
      _45_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _46_rCoerceMap;
      _46_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _47_coerceMapToArg;
      _47_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _48_types;
        _48_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi6 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _49_typeI = BigInteger.Zero; _49_typeI < _hi6; _49_typeI++) {
          DAST._ITypeArgDecl _50_typeParam;
          _50_typeParam = ((c).dtor_typeParams).Select(_49_typeI);
          DAST._IType _51_typeArg;
          RAST._ITypeParamDecl _52_rTypeParamDecl;
          DAST._IType _out8;
          RAST._ITypeParamDecl _out9;
          (this).GenTypeParam(_50_typeParam, out _out8, out _out9);
          _51_typeArg = _out8;
          _52_rTypeParamDecl = _out9;
          RAST._IType _53_rTypeArg;
          RAST._IType _out10;
          _out10 = (this).GenType(_51_typeArg, DCOMP.GenTypeContext.@default());
          _53_rTypeArg = _out10;
          _48_types = Dafny.Sequence<RAST._IType>.Concat(_48_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_53_rTypeArg))));
          if (((_49_typeI) < (new BigInteger((_6_variances).Count))) && (((_6_variances).Select(_49_typeI)).is_Nonvariant)) {
            _42_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_42_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_53_rTypeArg));
            goto continue_2_0;
          }
          DAST._ITypeArgDecl _54_coerceTypeParam;
          DAST._ITypeArgDecl _55_dt__update__tmp_h0 = _50_typeParam;
          Dafny.ISequence<Dafny.Rune> _56_dt__update_hname_h0 = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_49_typeI));
          _54_coerceTypeParam = DAST.TypeArgDecl.create(_56_dt__update_hname_h0, (_55_dt__update__tmp_h0).dtor_bounds, (_55_dt__update__tmp_h0).dtor_variance);
          DAST._IType _57_coerceTypeArg;
          RAST._ITypeParamDecl _58_rCoerceTypeParamDecl;
          DAST._IType _out11;
          RAST._ITypeParamDecl _out12;
          (this).GenTypeParam(_54_coerceTypeParam, out _out11, out _out12);
          _57_coerceTypeArg = _out11;
          _58_rCoerceTypeParamDecl = _out12;
          _45_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_45_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_51_typeArg, _57_coerceTypeArg)));
          RAST._IType _59_rCoerceType;
          RAST._IType _out13;
          _out13 = (this).GenType(_57_coerceTypeArg, DCOMP.GenTypeContext.@default());
          _59_rCoerceType = _out13;
          _46_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_46_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_53_rTypeArg, _59_rCoerceType)));
          _42_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_42_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_59_rCoerceType));
          _43_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_43_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_58_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _60_coerceFormal;
          _60_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_49_typeI));
          _47_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_47_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_53_rTypeArg, _59_rCoerceType), (RAST.Expr.create_Identifier(_60_coerceFormal)).Clone())));
          _44_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_44_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_60_coerceFormal, RAST.__default.Rc(RAST.Type.create_IntersectionType(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_53_rTypeArg), _59_rCoerceType)), RAST.__default.StaticTrait)))));
        continue_2_0: ;
        }
      after_2_0: ;
        _5_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_5_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_61_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _61_tpe);
})), _48_types)))));
      }
      bool _62_cIsEq;
      _62_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_62_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _4_datatypeName, _2_rTypeParamsDecls, _5_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_2_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _1_rTypeParams), _3_whereConstraints, _20_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _63_printImplBodyCases;
      _63_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _64_hashImplBodyCases;
      _64_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _65_coerceImplBodyCases;
      _65_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _66_i = BigInteger.Zero; _66_i < _hi7; _66_i++) {
        DAST._IDatatypeCtor _67_ctor;
        _67_ctor = ((c).dtor_ctors).Select(_66_i);
        Dafny.ISequence<Dafny.Rune> _68_ctorMatch;
        _68_ctorMatch = DCOMP.__default.escapeName((_67_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _69_modulePrefix;
        if (((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) {
          _69_modulePrefix = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        } else {
          _69_modulePrefix = Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."));
        }
        Dafny.ISequence<Dafny.Rune> _70_ctorName;
        _70_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_69_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_67_ctor).dtor_name));
        if (((new BigInteger((_70_ctorName).Count)) >= (new BigInteger(13))) && (((_70_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _70_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _71_printRhs;
        _71_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _70_ctorName), (((_67_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _72_hashRhs;
        _72_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        Dafny.ISequence<RAST._IAssignIdentifier> _73_coerceRhsArgs;
        _73_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _74_isNumeric;
        _74_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _75_ctorMatchInner;
        _75_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi8 = new BigInteger(((_67_ctor).dtor_args).Count);
        for (BigInteger _76_j = BigInteger.Zero; _76_j < _hi8; _76_j++) {
          DAST._IDatatypeDtor _77_dtor;
          _77_dtor = ((_67_ctor).dtor_args).Select(_76_j);
          Dafny.ISequence<Dafny.Rune> _78_patternName;
          _78_patternName = DCOMP.__default.escapeDtor(((_77_dtor).dtor_formal).dtor_name);
          Dafny.ISequence<Dafny.Rune> _79_fieldName;
          _79_fieldName = DCOMP.__default.escapeField(((_77_dtor).dtor_formal).dtor_name);
          DAST._IType _80_formalType;
          _80_formalType = ((_77_dtor).dtor_formal).dtor_typ;
          if (((_76_j).Sign == 0) && ((_79_fieldName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _74_isNumeric = true;
          }
          if (_74_isNumeric) {
            _79_fieldName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_77_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_76_j)));
          }
          if ((_80_formalType).is_Arrow) {
            _72_hashRhs = (_72_hashRhs).Then(((RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))));
          } else {
            _72_hashRhs = (_72_hashRhs).Then(((RAST.Expr.create_Identifier(_79_fieldName)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))));
          }
          _75_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_75_ctorMatchInner, ((_74_isNumeric) ? (_79_fieldName) : (_78_patternName))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_76_j).Sign == 1) {
            _71_printRhs = (_71_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _71_printRhs = (_71_printRhs).Then(RAST.Expr.create_RawExpr((((_80_formalType).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \"<function>\")?")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _79_fieldName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))))));
          RAST._IExpr _81_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _82_formalTpe;
          RAST._IType _out14;
          _out14 = (this).GenType(_80_formalType, DCOMP.GenTypeContext.@default());
          _82_formalTpe = _out14;
          DAST._IType _83_newFormalType;
          _83_newFormalType = (_80_formalType).Replace(_45_coerceMap);
          RAST._IType _84_newFormalTpe;
          _84_newFormalTpe = (_82_formalTpe).Replace(_46_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _85_upcastConverter;
          _85_upcastConverter = (this).UpcastConversionLambda(_80_formalType, _82_formalTpe, _83_newFormalType, _84_newFormalTpe, _47_coerceMapToArg);
          if ((_85_upcastConverter).is_Success) {
            RAST._IExpr _86_coercionFunction;
            _86_coercionFunction = (_85_upcastConverter).dtor_value;
            _81_coerceRhsArg = (_86_coercionFunction).Apply1(RAST.Expr.create_Identifier(_78_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_76_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _4_datatypeName));
            _81_coerceRhsArg = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("todo!"))).Apply1(RAST.Expr.create_LiteralString((this.error).dtor_value, false, false));
          }
          _73_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_73_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_78_patternName, _81_coerceRhsArg)));
        }
        RAST._IExpr _87_coerceRhs;
        _87_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_4_datatypeName)).MSel(DCOMP.__default.escapeName((_67_ctor).dtor_name)), _73_coerceRhsArgs);
        if (_74_isNumeric) {
          _68_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_68_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _75_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _68_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_68_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _75_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_67_ctor).dtor_hasAnyArgs) {
          _71_printRhs = (_71_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _71_printRhs = (_71_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _63_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_63_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _68_ctorMatch), RAST.Expr.create_Block(_71_printRhs))));
        _64_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_64_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _68_ctorMatch), RAST.Expr.create_Block(_72_hashRhs))));
        _65_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_65_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _68_ctorMatch), RAST.Expr.create_Block(_87_coerceRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IMatchCase> _88_extraCases;
        _88_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_4_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{"), (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}")))));
        _63_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_63_printImplBodyCases, _88_extraCases);
        _64_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_64_hashImplBodyCases, _88_extraCases);
        _65_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_65_coerceImplBodyCases, _88_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _89_defaultConstrainedTypeParams;
      _89_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_2_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _90_rTypeParamsDeclsWithEq;
      _90_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_2_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _91_rTypeParamsDeclsWithHash;
      _91_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_2_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _92_printImplBody;
      _92_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _63_printImplBodyCases);
      RAST._IExpr _93_hashImplBody;
      _93_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _64_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _1_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _1_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_92_printImplBody))))))));
      if ((new BigInteger((_43_rCoerceTypeParams).Count)).Sign == 1) {
        RAST._IExpr _94_coerceImplBody;
        _94_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _65_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_2_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _1_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), _43_rCoerceTypeParams, _44_coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _1_rTypeParams)), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _42_coerceTypes))))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.RcNew(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.Type.create_SelfOwned())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _42_coerceTypes)), _94_coerceImplBody))))))))));
      }
      if (_62_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_90_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _1_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_91_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _1_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_93_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _95_structName;
        _95_structName = (RAST.Expr.create_Identifier(_4_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _96_structAssignments;
        _96_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi9 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _97_i = BigInteger.Zero; _97_i < _hi9; _97_i++) {
          DAST._IDatatypeDtor _98_dtor;
          _98_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_97_i);
          _96_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_96_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_98_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _99_defaultConstrainedTypeParams;
        _99_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_2_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _100_fullType;
        _100_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _1_rTypeParams);
        if (_62_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_99_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _100_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_100_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_95_structName, _96_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_100_fullType), RAST.Type.create_Borrowed(_100_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
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
        BigInteger _hi0 = new BigInteger((p).Count);
        for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_0_i))));
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
        BigInteger _hi0 = new BigInteger((p).Count);
        for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_0_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, DCOMP._IGenTypeContext genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi0 = new BigInteger((args).Count);
      for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
        RAST._IType _1_genTp;
        RAST._IType _out0;
        _out0 = (this).GenType((args).Select(_0_i), genTypeContext);
        _1_genTp = _out0;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1_genTp));
      }
      return s;
    }
    public bool IsRcWrapped(Dafny.ISequence<DAST._IAttribute> attributes) {
      return ((!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("auto-nongrowing-size"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()))) && (!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false")))))) || ((attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true")))));
    }
    public RAST._IType GenType(DAST._IType c, DCOMP._IGenTypeContext genTypeContext)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source0 = c;
      {
        if (_source0.is_UserDefined) {
          DAST._IResolvedType _0_resolved = _source0.dtor_resolved;
          {
            RAST._IType _1_t;
            RAST._IType _out0;
            _out0 = DCOMP.COMP.GenPath((_0_resolved).dtor_path);
            _1_t = _out0;
            Dafny.ISequence<RAST._IType> _2_typeArgs;
            Dafny.ISequence<RAST._IType> _out1;
            _out1 = (this).GenTypeArgs((_0_resolved).dtor_typeArgs, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let9_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let9_0, _3_dt__update__tmp_h0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let10_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let10_0, _4_dt__update_hforTraitParents_h0 => DCOMP.GenTypeContext.create((_3_dt__update__tmp_h0).dtor_inBinding, (_3_dt__update__tmp_h0).dtor_inFn, _4_dt__update_hforTraitParents_h0))))));
            _2_typeArgs = _out1;
            s = RAST.Type.create_TypeApp(_1_t, _2_typeArgs);
            DAST._IResolvedTypeBase _source1 = (_0_resolved).dtor_kind;
            {
              if (_source1.is_Class) {
                {
                  s = (this).Object(s);
                }
                goto after_match1;
              }
            }
            {
              if (_source1.is_Datatype) {
                {
                  if ((this).IsRcWrapped((_0_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
                goto after_match1;
              }
            }
            {
              if (_source1.is_Trait) {
                {
                  if (((_0_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
                  }
                  if (!((genTypeContext).dtor_forTraitParents)) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
                goto after_match1;
              }
            }
            {
              DAST._IType _5_t = _source1.dtor_baseType;
              DAST._INewtypeRange _6_range = _source1.dtor_range;
              bool _7_erased = _source1.dtor_erase;
              {
                if (_7_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source2 = DCOMP.COMP.NewtypeToRustType(_5_t, _6_range);
                  {
                    if (_source2.is_Some) {
                      RAST._IType _8_v = _source2.dtor_value;
                      s = _8_v;
                      goto after_match2;
                    }
                  }
                  {
                  }
                after_match2: ;
                }
              }
            }
          after_match1: ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Object) {
          {
            s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
            if (!((genTypeContext).dtor_forTraitParents)) {
              s = (this).Object(RAST.Type.create_DynType(s));
            }
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Tuple) {
          Dafny.ISequence<DAST._IType> _9_types = _source0.dtor_Tuple_a0;
          {
            Dafny.ISequence<RAST._IType> _10_args;
            _10_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _11_i;
            _11_i = BigInteger.Zero;
            while ((_11_i) < (new BigInteger((_9_types).Count))) {
              RAST._IType _12_generated;
              RAST._IType _out2;
              _out2 = (this).GenType((_9_types).Select(_11_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let11_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let11_0, _13_dt__update__tmp_h1 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let12_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let12_0, _14_dt__update_hforTraitParents_h1 => DCOMP.GenTypeContext.create((_13_dt__update__tmp_h1).dtor_inBinding, (_13_dt__update__tmp_h1).dtor_inFn, _14_dt__update_hforTraitParents_h1))))));
              _12_generated = _out2;
              _10_args = Dafny.Sequence<RAST._IType>.Concat(_10_args, Dafny.Sequence<RAST._IType>.FromElements(_12_generated));
              _11_i = (_11_i) + (BigInteger.One);
            }
            if ((new BigInteger((_9_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) {
              s = RAST.Type.create_TupleType(_10_args);
            } else {
              s = RAST.__default.SystemTupleType(_10_args);
            }
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Array) {
          DAST._IType _15_element = _source0.dtor_element;
          BigInteger _16_dims = _source0.dtor_dims;
          {
            if ((_16_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _17_elem;
              RAST._IType _out3;
              _out3 = (this).GenType(_15_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let13_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let13_0, _18_dt__update__tmp_h2 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let14_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let14_0, _19_dt__update_hforTraitParents_h2 => DCOMP.GenTypeContext.create((_18_dt__update__tmp_h2).dtor_inBinding, (_18_dt__update__tmp_h2).dtor_inFn, _19_dt__update_hforTraitParents_h2))))));
              _17_elem = _out3;
              if ((_16_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_17_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _20_n;
                _20_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_16_dims));
                s = ((RAST.__default.dafny__runtime__type).MSel(_20_n)).Apply(Dafny.Sequence<RAST._IType>.FromElements(_17_elem));
                s = (this).Object(s);
              }
            }
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Seq) {
          DAST._IType _21_element = _source0.dtor_element;
          {
            RAST._IType _22_elem;
            RAST._IType _out4;
            _out4 = (this).GenType(_21_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let15_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let15_0, _23_dt__update__tmp_h3 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let16_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let16_0, _24_dt__update_hforTraitParents_h3 => DCOMP.GenTypeContext.create((_23_dt__update__tmp_h3).dtor_inBinding, (_23_dt__update__tmp_h3).dtor_inFn, _24_dt__update_hforTraitParents_h3))))));
            _22_elem = _out4;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_22_elem));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Set) {
          DAST._IType _25_element = _source0.dtor_element;
          {
            RAST._IType _26_elem;
            RAST._IType _out5;
            _out5 = (this).GenType(_25_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let17_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let17_0, _27_dt__update__tmp_h4 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let18_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let18_0, _28_dt__update_hforTraitParents_h4 => DCOMP.GenTypeContext.create((_27_dt__update__tmp_h4).dtor_inBinding, (_27_dt__update__tmp_h4).dtor_inFn, _28_dt__update_hforTraitParents_h4))))));
            _26_elem = _out5;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_26_elem));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Multiset) {
          DAST._IType _29_element = _source0.dtor_element;
          {
            RAST._IType _30_elem;
            RAST._IType _out6;
            _out6 = (this).GenType(_29_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let19_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let19_0, _31_dt__update__tmp_h5 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let20_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let20_0, _32_dt__update_hforTraitParents_h5 => DCOMP.GenTypeContext.create((_31_dt__update__tmp_h5).dtor_inBinding, (_31_dt__update__tmp_h5).dtor_inFn, _32_dt__update_hforTraitParents_h5))))));
            _30_elem = _out6;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_30_elem));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Map) {
          DAST._IType _33_key = _source0.dtor_key;
          DAST._IType _34_value = _source0.dtor_value;
          {
            RAST._IType _35_keyType;
            RAST._IType _out7;
            _out7 = (this).GenType(_33_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let21_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let21_0, _36_dt__update__tmp_h6 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let22_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let22_0, _37_dt__update_hforTraitParents_h6 => DCOMP.GenTypeContext.create((_36_dt__update__tmp_h6).dtor_inBinding, (_36_dt__update__tmp_h6).dtor_inFn, _37_dt__update_hforTraitParents_h6))))));
            _35_keyType = _out7;
            RAST._IType _38_valueType;
            RAST._IType _out8;
            _out8 = (this).GenType(_34_value, genTypeContext);
            _38_valueType = _out8;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_35_keyType, _38_valueType));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapBuilder) {
          DAST._IType _39_key = _source0.dtor_key;
          DAST._IType _40_value = _source0.dtor_value;
          {
            RAST._IType _41_keyType;
            RAST._IType _out9;
            _out9 = (this).GenType(_39_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let23_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let23_0, _42_dt__update__tmp_h7 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let24_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let24_0, _43_dt__update_hforTraitParents_h7 => DCOMP.GenTypeContext.create((_42_dt__update__tmp_h7).dtor_inBinding, (_42_dt__update__tmp_h7).dtor_inFn, _43_dt__update_hforTraitParents_h7))))));
            _41_keyType = _out9;
            RAST._IType _44_valueType;
            RAST._IType _out10;
            _out10 = (this).GenType(_40_value, genTypeContext);
            _44_valueType = _out10;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_41_keyType, _44_valueType));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SetBuilder) {
          DAST._IType _45_elem = _source0.dtor_element;
          {
            RAST._IType _46_elemType;
            RAST._IType _out11;
            _out11 = (this).GenType(_45_elem, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let25_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let25_0, _47_dt__update__tmp_h8 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let26_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let26_0, _48_dt__update_hforTraitParents_h8 => DCOMP.GenTypeContext.create((_47_dt__update__tmp_h8).dtor_inBinding, (_47_dt__update__tmp_h8).dtor_inFn, _48_dt__update_hforTraitParents_h8))))));
            _46_elemType = _out11;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_46_elemType));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Arrow) {
          Dafny.ISequence<DAST._IType> _49_args = _source0.dtor_args;
          DAST._IType _50_result = _source0.dtor_result;
          {
            Dafny.ISequence<RAST._IType> _51_argTypes;
            _51_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _52_i;
            _52_i = BigInteger.Zero;
            while ((_52_i) < (new BigInteger((_49_args).Count))) {
              RAST._IType _53_generated;
              RAST._IType _out12;
              _out12 = (this).GenType((_49_args).Select(_52_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let27_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let27_0, _54_dt__update__tmp_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let28_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let28_0, _55_dt__update_hforTraitParents_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(true, _pat_let29_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let29_0, _56_dt__update_hinFn_h0 => DCOMP.GenTypeContext.create((_54_dt__update__tmp_h9).dtor_inBinding, _56_dt__update_hinFn_h0, _55_dt__update_hforTraitParents_h9))))))));
              _53_generated = _out12;
              _51_argTypes = Dafny.Sequence<RAST._IType>.Concat(_51_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_53_generated)));
              _52_i = (_52_i) + (BigInteger.One);
            }
            RAST._IType _57_resultType;
            RAST._IType _out13;
            _out13 = (this).GenType(_50_result, DCOMP.GenTypeContext.create(((genTypeContext).dtor_inFn) || ((genTypeContext).dtor_inBinding), false, false));
            _57_resultType = _out13;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_51_argTypes, _57_resultType)));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source0.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _58_name = _h90;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_58_name));
          goto after_match0;
        }
      }
      {
        if (_source0.is_Primitive) {
          DAST._IPrimitive _59_p = _source0.dtor_Primitive_a0;
          {
            DAST._IPrimitive _source3 = _59_p;
            {
              if (_source3.is_Int) {
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
                goto after_match3;
              }
            }
            {
              if (_source3.is_Real) {
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
                goto after_match3;
              }
            }
            {
              if (_source3.is_String) {
                s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
                goto after_match3;
              }
            }
            {
              if (_source3.is_Bool) {
                s = RAST.Type.create_Bool();
                goto after_match3;
              }
            }
            {
              s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
            }
          after_match3: ;
          }
          goto after_match0;
        }
      }
      {
        Dafny.ISequence<Dafny.Rune> _60_v = _source0.dtor_Passthrough_a0;
        s = RAST.__default.RawType(_60_v);
      }
    after_match0: ;
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
      BigInteger _hi0 = new BigInteger((body).Count);
      for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
        DAST._IMethod _source0 = (body).Select(_0_i);
        {
          DAST._IMethod _1_m = _source0;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source1 = (_1_m).dtor_overridingPath;
            {
              if (_source1.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2_p = _source1.dtor_value;
                {
                  Dafny.ISequence<RAST._IImplMember> _3_existing;
                  _3_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_2_p)) {
                    _3_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_2_p);
                  }
                  if (((new BigInteger(((_1_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _4_genMethod;
                  RAST._IImplMember _out0;
                  _out0 = (this).GenMethod(_1_m, true, enclosingType, enclosingTypeParams);
                  _4_genMethod = _out0;
                  _3_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_3_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_4_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_2_p, _3_existing)));
                }
                goto after_match1;
              }
            }
            {
              {
                RAST._IImplMember _5_generated;
                RAST._IImplMember _out1;
                _out1 = (this).GenMethod(_1_m, forTrait, enclosingType, enclosingTypeParams);
                _5_generated = _out1;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_5_generated));
              }
            }
          after_match1: ;
          }
        }
      after_match0: ;
      }
    }
    public Dafny.ISequence<RAST._IFormal> GenParams(Dafny.ISequence<DAST._IFormal> @params)
    {
      Dafny.ISequence<RAST._IFormal> s = Dafny.Sequence<RAST._IFormal>.Empty;
      s = Dafny.Sequence<RAST._IFormal>.FromElements();
      BigInteger _hi0 = new BigInteger((@params).Count);
      for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
        DAST._IFormal _1_param;
        _1_param = (@params).Select(_0_i);
        RAST._IType _2_paramType;
        RAST._IType _out0;
        _out0 = (this).GenType((_1_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _2_paramType = _out0;
        if ((!((_2_paramType).CanReadWithoutClone())) && (!((_1_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _2_paramType = RAST.Type.create_Borrowed(_2_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_1_param).dtor_name), _2_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _0_params;
      Dafny.ISequence<RAST._IFormal> _out0;
      _out0 = (this).GenParams((m).dtor_params);
      _0_params = _out0;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1_paramNames;
      _1_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2_paramTypes;
      _2_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi0 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _3_paramI = BigInteger.Zero; _3_paramI < _hi0; _3_paramI++) {
        DAST._IFormal _4_dafny__formal;
        _4_dafny__formal = ((m).dtor_params).Select(_3_paramI);
        RAST._IFormal _5_formal;
        _5_formal = (_0_params).Select(_3_paramI);
        Dafny.ISequence<Dafny.Rune> _6_name;
        _6_name = (_5_formal).dtor_name;
        _1_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_6_name));
        _2_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2_paramTypes, _6_name, (_5_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _7_fnName;
      _7_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _8_selfIdent;
      _8_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _9_selfId;
        _9_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((m).dtor_outVarsAreUninitFieldsToAssign) {
          _9_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv0 = enclosingTypeParams;
        DAST._IType _10_instanceType;
        DAST._IType _source0 = enclosingType;
        {
          if (_source0.is_UserDefined) {
            DAST._IResolvedType _11_r = _source0.dtor_resolved;
            _10_instanceType = DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_11_r, _pat_let30_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let30_0, _12_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv0, _pat_let31_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let31_0, _13_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_12_dt__update__tmp_h0).dtor_path, _13_dt__update_htypeArgs_h0, (_12_dt__update__tmp_h0).dtor_kind, (_12_dt__update__tmp_h0).dtor_attributes, (_12_dt__update__tmp_h0).dtor_properMethods, (_12_dt__update__tmp_h0).dtor_extendedTypes))))));
            goto after_match0;
          }
        }
        {
          _10_instanceType = enclosingType;
        }
      after_match0: ;
        if (forTrait) {
          RAST._IFormal _14_selfFormal;
          if ((m).dtor_wasFunction) {
            _14_selfFormal = RAST.Formal.selfBorrowed;
          } else {
            _14_selfFormal = RAST.Formal.selfBorrowedMut;
          }
          _0_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_14_selfFormal), _0_params);
        } else {
          RAST._IType _15_tpe;
          RAST._IType _out1;
          _out1 = (this).GenType(_10_instanceType, DCOMP.GenTypeContext.@default());
          _15_tpe = _out1;
          if ((_9_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            _15_tpe = RAST.Type.create_Borrowed(_15_tpe);
          } else if ((_9_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_15_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _15_tpe = RAST.__default.SelfBorrowed;
              } else {
                _15_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              if ((((enclosingType).is_UserDefined) && ((((enclosingType).dtor_resolved).dtor_kind).is_Datatype)) && ((this).IsRcWrapped(((enclosingType).dtor_resolved).dtor_attributes))) {
                _15_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.Type.create_SelfOwned()));
              } else {
                _15_tpe = RAST.Type.create_Borrowed(RAST.Type.create_SelfOwned());
              }
            }
          }
          _0_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_9_selfId, _15_tpe)), _0_params);
        }
        _8_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_9_selfId, _10_instanceType);
      }
      Dafny.ISequence<RAST._IType> _16_retTypeArgs;
      _16_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _17_typeI;
      _17_typeI = BigInteger.Zero;
      while ((_17_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _18_typeExpr;
        RAST._IType _out2;
        _out2 = (this).GenType(((m).dtor_outTypes).Select(_17_typeI), DCOMP.GenTypeContext.@default());
        _18_typeExpr = _out2;
        _16_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_16_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_18_typeExpr));
        _17_typeI = (_17_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _19_visibility;
      if (forTrait) {
        _19_visibility = RAST.Visibility.create_PRIV();
      } else {
        _19_visibility = RAST.Visibility.create_PUB();
      }
      Dafny.ISequence<DAST._ITypeArgDecl> _20_typeParamsFiltered;
      _20_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi1 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _21_typeParamI = BigInteger.Zero; _21_typeParamI < _hi1; _21_typeParamI++) {
        DAST._ITypeArgDecl _22_typeParam;
        _22_typeParam = ((m).dtor_typeParams).Select(_21_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_22_typeParam).dtor_name)))) {
          _20_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_20_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_22_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _23_typeParams;
      _23_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_20_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi2 = new BigInteger((_20_typeParamsFiltered).Count);
        for (BigInteger _24_i = BigInteger.Zero; _24_i < _hi2; _24_i++) {
          DAST._IType _25_typeArg;
          RAST._ITypeParamDecl _26_rTypeParamDecl;
          DAST._IType _out3;
          RAST._ITypeParamDecl _out4;
          (this).GenTypeParam((_20_typeParamsFiltered).Select(_24_i), out _out3, out _out4);
          _25_typeArg = _out3;
          _26_rTypeParamDecl = _out4;
          RAST._ITypeParamDecl _27_dt__update__tmp_h1 = _26_rTypeParamDecl;
          Dafny.ISequence<RAST._IType> _28_dt__update_hconstraints_h0 = Dafny.Sequence<RAST._IType>.Concat((_26_rTypeParamDecl).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
          _26_rTypeParamDecl = RAST.TypeParamDecl.create((_27_dt__update__tmp_h1).dtor_content, _28_dt__update_hconstraints_h0);
          _23_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_23_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_26_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _29_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _30_env = DCOMP.Environment.Default();
      RAST._IExpr _31_preBody;
      _31_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _32_preAssignNames;
      _32_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _33_preAssignTypes;
      _33_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _34_earlyReturn;
        _34_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None();
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source1 = (m).dtor_outVars;
        {
          if (_source1.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _35_outVars = _source1.dtor_value;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _34_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
                BigInteger _hi3 = new BigInteger((_35_outVars).Count);
                for (BigInteger _36_outI = BigInteger.Zero; _36_outI < _hi3; _36_outI++) {
                  Dafny.ISequence<Dafny.Rune> _37_outVar;
                  _37_outVar = (_35_outVars).Select(_36_outI);
                  Dafny.ISequence<Dafny.Rune> _38_outName;
                  _38_outName = DCOMP.__default.escapeName((_37_outVar));
                  Dafny.ISequence<Dafny.Rune> _39_tracker__name;
                  _39_tracker__name = DCOMP.__default.AddAssignedPrefix(_38_outName);
                  _32_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_32_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_39_tracker__name));
                  _33_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_33_preAssignTypes, _39_tracker__name, RAST.Type.create_Bool());
                  _31_preBody = (_31_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _39_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _40_tupleArgs;
                _40_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
                BigInteger _hi4 = new BigInteger((_35_outVars).Count);
                for (BigInteger _41_outI = BigInteger.Zero; _41_outI < _hi4; _41_outI++) {
                  Dafny.ISequence<Dafny.Rune> _42_outVar;
                  _42_outVar = (_35_outVars).Select(_41_outI);
                  RAST._IType _43_outType;
                  RAST._IType _out5;
                  _out5 = (this).GenType(((m).dtor_outTypes).Select(_41_outI), DCOMP.GenTypeContext.@default());
                  _43_outType = _out5;
                  Dafny.ISequence<Dafny.Rune> _44_outName;
                  _44_outName = DCOMP.__default.escapeName((_42_outVar));
                  _1_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_44_outName));
                  RAST._IType _45_outMaybeType;
                  if ((_43_outType).CanReadWithoutClone()) {
                    _45_outMaybeType = _43_outType;
                  } else {
                    _45_outMaybeType = RAST.__default.MaybePlaceboType(_43_outType);
                  }
                  _2_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2_paramTypes, _44_outName, _45_outMaybeType);
                  _40_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_40_tupleArgs, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_44_outName));
                }
                _34_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(_40_tupleArgs);
              }
            }
            goto after_match1;
          }
        }
        {
        }
      after_match1: ;
        _30_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_32_preAssignNames, _1_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_33_preAssignTypes, _2_paramTypes));
        RAST._IExpr _46_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _47___v69;
        DCOMP._IEnvironment _48___v70;
        RAST._IExpr _out6;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out7;
        DCOMP._IEnvironment _out8;
        (this).GenStmts((m).dtor_body, _8_selfIdent, _30_env, true, _34_earlyReturn, out _out6, out _out7, out _out8);
        _46_body = _out6;
        _47___v69 = _out7;
        _48___v70 = _out8;
        _29_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_31_preBody).Then(_46_body));
      } else {
        _30_env = DCOMP.Environment.create(_1_paramNames, _2_paramTypes);
        _29_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_19_visibility, RAST.Fn.create(_7_fnName, _23_typeParams, _0_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_16_retTypeArgs).Count)) == (BigInteger.One)) ? ((_16_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_16_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _29_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _0_declarations;
      _0_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1_i;
      _1_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _2_stmts;
      _2_stmts = stmts;
      while ((_1_i) < (new BigInteger((_2_stmts).Count))) {
        DAST._IStatement _3_stmt;
        _3_stmt = (_2_stmts).Select(_1_i);
        DAST._IStatement _source0 = _3_stmt;
        {
          if (_source0.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _4_name = _source0.dtor_name;
            DAST._IType _5_optType = _source0.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source0.dtor_maybeValue;
            if (maybeValue0.is_None) {
              if (((_1_i) + (BigInteger.One)) < (new BigInteger((_2_stmts).Count))) {
                DAST._IStatement _source1 = (_2_stmts).Select((_1_i) + (BigInteger.One));
                {
                  if (_source1.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source1.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> ident0 = lhs0.dtor_ident;
                      Dafny.ISequence<Dafny.Rune> _6_name2 = ident0;
                      DAST._IExpression _7_rhs = _source1.dtor_value;
                      if (object.Equals(_6_name2, _4_name)) {
                        _2_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_2_stmts).Subsequence(BigInteger.Zero, _1_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_4_name, _5_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_7_rhs)))), (_2_stmts).Drop((_1_i) + (new BigInteger(2))));
                        _3_stmt = (_2_stmts).Select(_1_i);
                      }
                      goto after_match1;
                    }
                  }
                }
                {
                }
              after_match1: ;
              }
              goto after_match0;
            }
          }
        }
        {
        }
      after_match0: ;
        RAST._IExpr _8_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _9_recIdents;
        DCOMP._IEnvironment _10_newEnv2;
        RAST._IExpr _out0;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1;
        DCOMP._IEnvironment _out2;
        (this).GenStmt(_3_stmt, selfIdent, newEnv, (isLast) && ((_1_i) == ((new BigInteger((_2_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out0, out _out1, out _out2);
        _8_stmtExpr = _out0;
        _9_recIdents = _out1;
        _10_newEnv2 = _out2;
        newEnv = _10_newEnv2;
        DAST._IStatement _source2 = _3_stmt;
        {
          if (_source2.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _11_name = _source2.dtor_name;
            {
              _0_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_0_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_11_name)));
            }
            goto after_match2;
          }
        }
        {
        }
      after_match2: ;
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_9_recIdents, _0_declarations));
        generated = (generated).Then(_8_stmtExpr);
        _1_i = (_1_i) + (BigInteger.One);
        if ((_8_stmtExpr).is_Return) {
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
      DAST._IAssignLhs _source0 = lhs;
      {
        if (_source0.is_Ident) {
          Dafny.ISequence<Dafny.Rune> ident0 = _source0.dtor_ident;
          Dafny.ISequence<Dafny.Rune> _0_id = ident0;
          {
            Dafny.ISequence<Dafny.Rune> _1_idRust;
            _1_idRust = DCOMP.__default.escapeName(_0_id);
            if (((env).IsBorrowed(_1_idRust)) || ((env).IsBorrowedMut(_1_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1_idRust);
            needsIIFE = false;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Select) {
          DAST._IExpression _2_on = _source0.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _3_field = _source0.dtor_field;
          {
            Dafny.ISequence<Dafny.Rune> _4_fieldName;
            _4_fieldName = DCOMP.__default.escapeName(_3_field);
            RAST._IExpr _5_onExpr;
            DCOMP._IOwnership _6_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _7_recIdents;
            RAST._IExpr _out0;
            DCOMP._IOwnership _out1;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2;
            (this).GenExpr(_2_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out0, out _out1, out _out2);
            _5_onExpr = _out0;
            _6_onOwned = _out1;
            _7_recIdents = _out2;
            RAST._IExpr _source1 = _5_onExpr;
            {
              bool disjunctiveMatch0 = false;
              if (_source1.is_Call) {
                RAST._IExpr obj0 = _source1.dtor_obj;
                if (obj0.is_Select) {
                  RAST._IExpr obj1 = obj0.dtor_obj;
                  if (obj1.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name0 = obj1.dtor_name;
                    if (object.Equals(name0, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      Dafny.ISequence<Dafny.Rune> name1 = obj0.dtor_name;
                      if (object.Equals(name1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))) {
                        disjunctiveMatch0 = true;
                      }
                    }
                  }
                }
              }
              if (_source1.is_Identifier) {
                Dafny.ISequence<Dafny.Rune> name2 = _source1.dtor_name;
                if (object.Equals(name2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                  disjunctiveMatch0 = true;
                }
              }
              if (_source1.is_UnaryOp) {
                Dafny.ISequence<Dafny.Rune> op10 = _source1.dtor_op1;
                if (object.Equals(op10, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                  RAST._IExpr underlying0 = _source1.dtor_underlying;
                  if (underlying0.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name3 = underlying0.dtor_name;
                    if (object.Equals(name3, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      disjunctiveMatch0 = true;
                    }
                  }
                }
              }
              if (disjunctiveMatch0) {
                Dafny.ISequence<Dafny.Rune> _8_isAssignedVar;
                _8_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_4_fieldName);
                if (((newEnv).dtor_names).Contains(_8_isAssignedVar)) {
                  generated = ((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_4_fieldName), RAST.Expr.create_Identifier(_8_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_8_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _8_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _4_fieldName, rhs);
                }
                goto after_match1;
              }
            }
            {
              if (!object.Equals(_5_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _5_onExpr = ((this).modify__macro).Apply1(_5_onExpr);
              }
              generated = RAST.__default.AssignMember(_5_onExpr, _4_fieldName, rhs);
            }
          after_match1: ;
            readIdents = _7_recIdents;
            needsIIFE = false;
          }
          goto after_match0;
        }
      }
      {
        DAST._IExpression _9_on = _source0.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _10_indices = _source0.dtor_indices;
        {
          RAST._IExpr _11_onExpr;
          DCOMP._IOwnership _12_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _13_recIdents;
          RAST._IExpr _out3;
          DCOMP._IOwnership _out4;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out5;
          (this).GenExpr(_9_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out3, out _out4, out _out5);
          _11_onExpr = _out3;
          _12_onOwned = _out4;
          _13_recIdents = _out5;
          readIdents = _13_recIdents;
          _11_onExpr = ((this).modify__macro).Apply1(_11_onExpr);
          RAST._IExpr _14_r;
          _14_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _15_indicesExpr;
          _15_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi0 = new BigInteger((_10_indices).Count);
          for (BigInteger _16_i = BigInteger.Zero; _16_i < _hi0; _16_i++) {
            RAST._IExpr _17_idx;
            DCOMP._IOwnership _18___v79;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _19_recIdentsIdx;
            RAST._IExpr _out6;
            DCOMP._IOwnership _out7;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out8;
            (this).GenExpr((_10_indices).Select(_16_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out6, out _out7, out _out8);
            _17_idx = _out6;
            _18___v79 = _out7;
            _19_recIdentsIdx = _out8;
            Dafny.ISequence<Dafny.Rune> _20_varName;
            _20_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_16_i));
            _15_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_15_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_20_varName)));
            _14_r = (_14_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _20_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.IntoUsize(_17_idx))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _19_recIdentsIdx);
          }
          if ((new BigInteger((_10_indices).Count)) > (BigInteger.One)) {
            _11_onExpr = (_11_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _21_rhs;
          _21_rhs = rhs;
          var _pat_let_tv0 = env;
          if (((_11_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_11_onExpr).LhsIdentifierName(), _pat_let32_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let32_0, _22_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv0).GetType(_22_name), _pat_let33_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let33_0, _23_tpe => ((_23_tpe).is_Some) && (((_23_tpe).dtor_value).IsUninitArray())))))))) {
            _21_rhs = RAST.__default.MaybeUninitNew(_21_rhs);
          }
          generated = (_14_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_11_onExpr, _15_indicesExpr)), _21_rhs));
          needsIIFE = true;
        }
      }
    after_match0: ;
    }
    public void GenStmt(DAST._IStatement stmt, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source0 = stmt;
      {
        if (_source0.is_ConstructorNewSeparator) {
          Dafny.ISequence<DAST._IFormal> _0_fields = _source0.dtor_fields;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi0 = new BigInteger((_0_fields).Count);
            for (BigInteger _1_i = BigInteger.Zero; _1_i < _hi0; _1_i++) {
              DAST._IFormal _2_field;
              _2_field = (_0_fields).Select(_1_i);
              Dafny.ISequence<Dafny.Rune> _3_fieldName;
              _3_fieldName = DCOMP.__default.escapeName((_2_field).dtor_name);
              RAST._IType _4_fieldTyp;
              RAST._IType _out0;
              _out0 = (this).GenType((_2_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _4_fieldTyp = _out0;
              Dafny.ISequence<Dafny.Rune> _5_isAssignedVar;
              _5_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_3_fieldName);
              if (((newEnv).dtor_names).Contains(_5_isAssignedVar)) {
                RAST._IExpr _6_rhs;
                DCOMP._IOwnership _7___v80;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _8___v81;
                RAST._IExpr _out1;
                DCOMP._IOwnership _out2;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out3;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_2_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1, out _out2, out _out3);
                _6_rhs = _out1;
                _7___v80 = _out2;
                _8___v81 = _out3;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_5_isAssignedVar));
                generated = (generated).Then(((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_3_fieldName), RAST.Expr.create_Identifier(_5_isAssignedVar), _6_rhs)));
                newEnv = (newEnv).RemoveAssigned(_5_isAssignedVar);
              }
            }
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _9_name = _source0.dtor_name;
          DAST._IType _10_typ = _source0.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source0.dtor_maybeValue;
          if (maybeValue0.is_Some) {
            DAST._IExpression _11_expression = maybeValue0.dtor_value;
            {
              RAST._IType _12_tpe;
              RAST._IType _out4;
              _out4 = (this).GenType(_10_typ, DCOMP.GenTypeContext.InBinding());
              _12_tpe = _out4;
              Dafny.ISequence<Dafny.Rune> _13_varName;
              _13_varName = DCOMP.__default.escapeName(_9_name);
              bool _14_hasCopySemantics;
              _14_hasCopySemantics = (_12_tpe).CanReadWithoutClone();
              if (((_11_expression).is_InitializationValue) && (!(_14_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _13_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).ApplyType1(_12_tpe)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_13_varName, RAST.__default.MaybePlaceboType(_12_tpe));
              } else {
                RAST._IExpr _15_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _16_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_11_expression).is_InitializationValue) && ((_12_tpe).IsObjectOrPointer())) {
                  _15_expr = (_12_tpe).ToNullExpr();
                  _16_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _17_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out5;
                  DCOMP._IOwnership _out6;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out7;
                  (this).GenExpr(_11_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out5, out _out6, out _out7);
                  _15_expr = _out5;
                  _17_exprOwnership = _out6;
                  _16_recIdents = _out7;
                }
                readIdents = _16_recIdents;
                if ((_11_expression).is_NewUninitArray) {
                  _12_tpe = (_12_tpe).TypeAtInitialization();
                } else {
                  _12_tpe = _12_tpe;
                }
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_9_name), Std.Wrappers.Option<RAST._IType>.create_Some(_12_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_15_expr));
                newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_9_name), _12_tpe);
              }
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _18_name = _source0.dtor_name;
          DAST._IType _19_typ = _source0.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source0.dtor_maybeValue;
          if (maybeValue1.is_None) {
            {
              DAST._IStatement _20_newStmt;
              _20_newStmt = DAST.Statement.create_DeclareVar(_18_name, _19_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_19_typ)));
              RAST._IExpr _out8;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out9;
              DCOMP._IEnvironment _out10;
              (this).GenStmt(_20_newStmt, selfIdent, env, isLast, earlyReturn, out _out8, out _out9, out _out10);
              generated = _out8;
              readIdents = _out9;
              newEnv = _out10;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_Assign) {
          DAST._IAssignLhs _21_lhs = _source0.dtor_lhs;
          DAST._IExpression _22_expression = _source0.dtor_value;
          {
            RAST._IExpr _23_exprGen;
            DCOMP._IOwnership _24___v82;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _25_exprIdents;
            RAST._IExpr _out11;
            DCOMP._IOwnership _out12;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out13;
            (this).GenExpr(_22_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out11, out _out12, out _out13);
            _23_exprGen = _out11;
            _24___v82 = _out12;
            _25_exprIdents = _out13;
            if ((_21_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _26_rustId;
              _26_rustId = DCOMP.__default.escapeName(((_21_lhs).dtor_ident));
              Std.Wrappers._IOption<RAST._IType> _27_tpe;
              _27_tpe = (env).GetType(_26_rustId);
              if (((_27_tpe).is_Some) && ((((_27_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _23_exprGen = RAST.__default.MaybePlacebo(_23_exprGen);
              }
            }
            if (((_21_lhs).is_Index) && (((_21_lhs).dtor_expr).is_Ident)) {
              Dafny.ISequence<Dafny.Rune> _28_rustId;
              _28_rustId = DCOMP.__default.escapeName(((_21_lhs).dtor_expr).dtor_name);
              Std.Wrappers._IOption<RAST._IType> _29_tpe;
              _29_tpe = (env).GetType(_28_rustId);
              if (((_29_tpe).is_Some) && ((((_29_tpe).dtor_value).ExtractMaybeUninitArrayElement()).is_Some)) {
                _23_exprGen = RAST.__default.MaybeUninitNew(_23_exprGen);
              }
            }
            RAST._IExpr _30_lhsGen;
            bool _31_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _32_recIdents;
            DCOMP._IEnvironment _33_resEnv;
            RAST._IExpr _out14;
            bool _out15;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out16;
            DCOMP._IEnvironment _out17;
            (this).GenAssignLhs(_21_lhs, _23_exprGen, selfIdent, env, out _out14, out _out15, out _out16, out _out17);
            _30_lhsGen = _out14;
            _31_needsIIFE = _out15;
            _32_recIdents = _out16;
            _33_resEnv = _out17;
            generated = _30_lhsGen;
            newEnv = _33_resEnv;
            if (_31_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_32_recIdents, _25_exprIdents);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_If) {
          DAST._IExpression _34_cond = _source0.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _35_thnDafny = _source0.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _36_elsDafny = _source0.dtor_els;
          {
            RAST._IExpr _37_cond;
            DCOMP._IOwnership _38___v83;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _39_recIdents;
            RAST._IExpr _out18;
            DCOMP._IOwnership _out19;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out20;
            (this).GenExpr(_34_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out18, out _out19, out _out20);
            _37_cond = _out18;
            _38___v83 = _out19;
            _39_recIdents = _out20;
            Dafny.ISequence<Dafny.Rune> _40_condString;
            _40_condString = (_37_cond)._ToString(DCOMP.__default.IND);
            readIdents = _39_recIdents;
            RAST._IExpr _41_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _42_thnIdents;
            DCOMP._IEnvironment _43_thnEnv;
            RAST._IExpr _out21;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out22;
            DCOMP._IEnvironment _out23;
            (this).GenStmts(_35_thnDafny, selfIdent, env, isLast, earlyReturn, out _out21, out _out22, out _out23);
            _41_thn = _out21;
            _42_thnIdents = _out22;
            _43_thnEnv = _out23;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _42_thnIdents);
            RAST._IExpr _44_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _45_elsIdents;
            DCOMP._IEnvironment _46_elsEnv;
            RAST._IExpr _out24;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out25;
            DCOMP._IEnvironment _out26;
            (this).GenStmts(_36_elsDafny, selfIdent, env, isLast, earlyReturn, out _out24, out _out25, out _out26);
            _44_els = _out24;
            _45_elsIdents = _out25;
            _46_elsEnv = _out26;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _45_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_37_cond, _41_thn, _44_els);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _47_lbl = _source0.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _48_body = _source0.dtor_body;
          {
            RAST._IExpr _49_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _50_bodyIdents;
            DCOMP._IEnvironment _51_env2;
            RAST._IExpr _out27;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out28;
            DCOMP._IEnvironment _out29;
            (this).GenStmts(_48_body, selfIdent, env, isLast, earlyReturn, out _out27, out _out28, out _out29);
            _49_body = _out27;
            _50_bodyIdents = _out28;
            _51_env2 = _out29;
            readIdents = _50_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _47_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_49_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_While) {
          DAST._IExpression _52_cond = _source0.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _53_body = _source0.dtor_body;
          {
            RAST._IExpr _54_cond;
            DCOMP._IOwnership _55___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _56_recIdents;
            RAST._IExpr _out30;
            DCOMP._IOwnership _out31;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
            (this).GenExpr(_52_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
            _54_cond = _out30;
            _55___v84 = _out31;
            _56_recIdents = _out32;
            readIdents = _56_recIdents;
            RAST._IExpr _57_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _58_bodyIdents;
            DCOMP._IEnvironment _59_bodyEnv;
            RAST._IExpr _out33;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out34;
            DCOMP._IEnvironment _out35;
            (this).GenStmts(_53_body, selfIdent, env, false, earlyReturn, out _out33, out _out34, out _out35);
            _57_bodyExpr = _out33;
            _58_bodyIdents = _out34;
            _59_bodyEnv = _out35;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _58_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_54_cond), _57_bodyExpr);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _60_boundName = _source0.dtor_boundName;
          DAST._IType _61_boundType = _source0.dtor_boundType;
          DAST._IExpression _62_overExpr = _source0.dtor_over;
          Dafny.ISequence<DAST._IStatement> _63_body = _source0.dtor_body;
          {
            RAST._IExpr _64_over;
            DCOMP._IOwnership _65___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _66_recIdents;
            RAST._IExpr _out36;
            DCOMP._IOwnership _out37;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out38;
            (this).GenExpr(_62_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out36, out _out37, out _out38);
            _64_over = _out36;
            _65___v85 = _out37;
            _66_recIdents = _out38;
            if (((_62_overExpr).is_MapBoundedPool) || ((_62_overExpr).is_SetBoundedPool)) {
              _64_over = ((_64_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _67_boundTpe;
            RAST._IType _out39;
            _out39 = (this).GenType(_61_boundType, DCOMP.GenTypeContext.@default());
            _67_boundTpe = _out39;
            readIdents = _66_recIdents;
            Dafny.ISequence<Dafny.Rune> _68_boundRName;
            _68_boundRName = DCOMP.__default.escapeName(_60_boundName);
            RAST._IExpr _69_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _70_bodyIdents;
            DCOMP._IEnvironment _71_bodyEnv;
            RAST._IExpr _out40;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out41;
            DCOMP._IEnvironment _out42;
            (this).GenStmts(_63_body, selfIdent, (env).AddAssigned(_68_boundRName, _67_boundTpe), false, earlyReturn, out _out40, out _out41, out _out42);
            _69_bodyExpr = _out40;
            _70_bodyIdents = _out41;
            _71_bodyEnv = _out42;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _70_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_68_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_68_boundRName, _64_over, _69_bodyExpr);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _72_toLabel = _source0.dtor_toLabel;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source1 = _72_toLabel;
            {
              if (_source1.is_Some) {
                Dafny.ISequence<Dafny.Rune> _73_lbl = _source1.dtor_value;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _73_lbl)));
                }
                goto after_match1;
              }
            }
            {
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
          after_match1: ;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _74_body = _source0.dtor_body;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _75_selfClone;
              DCOMP._IOwnership _76___v86;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _77___v87;
              RAST._IExpr _out43;
              DCOMP._IOwnership _out44;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out45;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out43, out _out44, out _out45);
              _75_selfClone = _out43;
              _76___v86 = _out44;
              _77___v87 = _out45;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_75_selfClone)));
            }
            newEnv = env;
            BigInteger _hi1 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _78_paramI = BigInteger.Zero; _78_paramI < _hi1; _78_paramI++) {
              Dafny.ISequence<Dafny.Rune> _79_param;
              _79_param = ((env).dtor_names).Select(_78_paramI);
              RAST._IExpr _80_paramInit;
              DCOMP._IOwnership _81___v88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _82___v89;
              RAST._IExpr _out46;
              DCOMP._IOwnership _out47;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out48;
              (this).GenIdent(_79_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out46, out _out47, out _out48);
              _80_paramInit = _out46;
              _81___v88 = _out47;
              _82___v89 = _out48;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _79_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_80_paramInit)));
              if (((env).dtor_types).Contains(_79_param)) {
                RAST._IType _83_declaredType;
                _83_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_79_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_79_param, _83_declaredType);
              }
            }
            RAST._IExpr _84_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _85_bodyIdents;
            DCOMP._IEnvironment _86_bodyEnv;
            RAST._IExpr _out49;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out50;
            DCOMP._IEnvironment _out51;
            (this).GenStmts(_74_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out49, out _out50, out _out51);
            _84_bodyExpr = _out49;
            _85_bodyIdents = _out50;
            _86_bodyEnv = _out51;
            readIdents = _85_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _84_bodyExpr)));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_JumpTailCallStart) {
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Call) {
          DAST._IExpression _87_on = _source0.dtor_on;
          DAST._ICallName _88_name = _source0.dtor_callName;
          Dafny.ISequence<DAST._IType> _89_typeArgs = _source0.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _90_args = _source0.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _91_maybeOutVars = _source0.dtor_outs;
          {
            Dafny.ISequence<RAST._IExpr> _92_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _93_recIdents;
            Dafny.ISequence<RAST._IType> _94_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _95_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out52;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out53;
            Dafny.ISequence<RAST._IType> _out54;
            Std.Wrappers._IOption<DAST._IResolvedType> _out55;
            (this).GenArgs(selfIdent, _88_name, _89_typeArgs, _90_args, env, out _out52, out _out53, out _out54, out _out55);
            _92_argExprs = _out52;
            _93_recIdents = _out53;
            _94_typeExprs = _out54;
            _95_fullNameQualifier = _out55;
            readIdents = _93_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source2 = _95_fullNameQualifier;
            {
              if (_source2.is_Some) {
                DAST._IResolvedType value0 = _source2.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _96_path = value0.dtor_path;
                Dafny.ISequence<DAST._IType> _97_onTypeArgs = value0.dtor_typeArgs;
                DAST._IResolvedTypeBase _98_base = value0.dtor_kind;
                RAST._IExpr _99_fullPath;
                RAST._IExpr _out56;
                _out56 = DCOMP.COMP.GenPathExpr(_96_path);
                _99_fullPath = _out56;
                Dafny.ISequence<RAST._IType> _100_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out57;
                _out57 = (this).GenTypeArgs(_97_onTypeArgs, DCOMP.GenTypeContext.@default());
                _100_onTypeExprs = _out57;
                RAST._IExpr _101_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _102_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _103_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_98_base).is_Trait) || ((_98_base).is_Class)) {
                  RAST._IExpr _out58;
                  DCOMP._IOwnership _out59;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out60;
                  (this).GenExpr(_87_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out58, out _out59, out _out60);
                  _101_onExpr = _out58;
                  _102_recOwnership = _out59;
                  _103_recIdents = _out60;
                  _101_onExpr = ((this).modify__macro).Apply1(_101_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _103_recIdents);
                } else {
                  RAST._IExpr _out61;
                  DCOMP._IOwnership _out62;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out63;
                  (this).GenExpr(_87_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out61, out _out62, out _out63);
                  _101_onExpr = _out61;
                  _102_recOwnership = _out62;
                  _103_recIdents = _out63;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _103_recIdents);
                }
                generated = ((((_99_fullPath).ApplyType(_100_onTypeExprs)).MSel(DCOMP.__default.escapeName((_88_name).dtor_name))).ApplyType(_94_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_101_onExpr), _92_argExprs));
                goto after_match2;
              }
            }
            {
              RAST._IExpr _104_onExpr;
              DCOMP._IOwnership _105___v94;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _106_enclosingIdents;
              RAST._IExpr _out64;
              DCOMP._IOwnership _out65;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out66;
              (this).GenExpr(_87_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out64, out _out65, out _out66);
              _104_onExpr = _out64;
              _105___v94 = _out65;
              _106_enclosingIdents = _out66;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _106_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _107_renderedName;
              DAST._ICallName _source3 = _88_name;
              {
                if (_source3.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _108_name = _source3.dtor_name;
                  _107_renderedName = DCOMP.__default.escapeName(_108_name);
                  goto after_match3;
                }
              }
              {
                bool disjunctiveMatch0 = false;
                if (_source3.is_MapBuilderAdd) {
                  disjunctiveMatch0 = true;
                }
                if (_source3.is_SetBuilderAdd) {
                  disjunctiveMatch0 = true;
                }
                if (disjunctiveMatch0) {
                  _107_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                  goto after_match3;
                }
              }
              {
                _107_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
              }
            after_match3: ;
              DAST._IExpression _source4 = _87_on;
              {
                if (_source4.is_Companion) {
                  {
                    _104_onExpr = (_104_onExpr).MSel(_107_renderedName);
                  }
                  goto after_match4;
                }
              }
              {
                {
                  if (!object.Equals(_104_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source5 = _88_name;
                    {
                      if (_source5.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source5.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _109_tpe = onType0.dtor_value;
                          RAST._IType _110_typ;
                          RAST._IType _out67;
                          _out67 = (this).GenType(_109_tpe, DCOMP.GenTypeContext.@default());
                          _110_typ = _out67;
                          if (((_110_typ).IsObjectOrPointer()) && (!object.Equals(_104_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _104_onExpr = ((this).modify__macro).Apply1(_104_onExpr);
                          }
                          goto after_match5;
                        }
                      }
                    }
                    {
                    }
                  after_match5: ;
                  }
                  _104_onExpr = (_104_onExpr).Sel(_107_renderedName);
                }
              }
            after_match4: ;
              generated = ((_104_onExpr).ApplyType(_94_typeExprs)).Apply(_92_argExprs);
            }
          after_match2: ;
            if (((_91_maybeOutVars).is_Some) && ((new BigInteger(((_91_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _111_outVar;
              _111_outVar = DCOMP.__default.escapeName((((_91_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
              if (!((env).CanReadWithoutClone(_111_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_111_outVar, generated);
            } else if (((_91_maybeOutVars).is_None) || ((new BigInteger(((_91_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _112_tmpVar;
              _112_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _113_tmpId;
              _113_tmpId = RAST.Expr.create_Identifier(_112_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _112_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _114_outVars;
              _114_outVars = (_91_maybeOutVars).dtor_value;
              BigInteger _hi2 = new BigInteger((_114_outVars).Count);
              for (BigInteger _115_outI = BigInteger.Zero; _115_outI < _hi2; _115_outI++) {
                Dafny.ISequence<Dafny.Rune> _116_outVar;
                _116_outVar = DCOMP.__default.escapeName(((_114_outVars).Select(_115_outI)));
                RAST._IExpr _117_rhs;
                _117_rhs = (_113_tmpId).Sel(Std.Strings.__default.OfNat(_115_outI));
                if (!((env).CanReadWithoutClone(_116_outVar))) {
                  _117_rhs = RAST.__default.MaybePlacebo(_117_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_116_outVar, _117_rhs));
              }
            }
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Return) {
          DAST._IExpression _118_exprDafny = _source0.dtor_expr;
          {
            RAST._IExpr _119_expr;
            DCOMP._IOwnership _120___v105;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _121_recIdents;
            RAST._IExpr _out68;
            DCOMP._IOwnership _out69;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out70;
            (this).GenExpr(_118_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out68, out _out69, out _out70);
            _119_expr = _out68;
            _120___v105 = _out69;
            _121_recIdents = _out70;
            readIdents = _121_recIdents;
            if (isLast) {
              generated = _119_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_119_expr));
            }
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_EarlyReturn) {
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source6 = earlyReturn;
            {
              if (_source6.is_None) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
                goto after_match6;
              }
            }
            {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _122_rustIdents = _source6.dtor_value;
              Dafny.ISequence<RAST._IExpr> _123_tupleArgs;
              _123_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi3 = new BigInteger((_122_rustIdents).Count);
              for (BigInteger _124_i = BigInteger.Zero; _124_i < _hi3; _124_i++) {
                RAST._IExpr _125_rIdent;
                DCOMP._IOwnership _126___v106;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _127___v107;
                RAST._IExpr _out71;
                DCOMP._IOwnership _out72;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out73;
                (this).GenIdent((_122_rustIdents).Select(_124_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out71, out _out72, out _out73);
                _125_rIdent = _out71;
                _126___v106 = _out72;
                _127___v107 = _out73;
                _123_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_123_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_125_rIdent));
              }
              if ((new BigInteger((_123_tupleArgs).Count)) == (BigInteger.One)) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_123_tupleArgs).Select(BigInteger.Zero)));
              } else {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_123_tupleArgs)));
              }
            }
          after_match6: ;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Halt) {
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        DAST._IExpression _128_e = _source0.dtor_Print_a0;
        {
          RAST._IExpr _129_printedExpr;
          DCOMP._IOwnership _130_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _131_recIdents;
          RAST._IExpr _out74;
          DCOMP._IOwnership _out75;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out76;
          (this).GenExpr(_128_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out74, out _out75, out _out76);
          _129_printedExpr = _out74;
          _130_recOwnership = _out75;
          _131_recIdents = _out76;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_129_printedExpr)));
          readIdents = _131_recIdents;
          newEnv = env;
        }
      }
    after_match0: ;
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source0 = range;
      {
        if (_source0.is_NoRange) {
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      {
        if (_source0.is_U8) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      {
        if (_source0.is_U16) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      {
        if (_source0.is_U32) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      {
        if (_source0.is_U64) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      {
        if (_source0.is_U128) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      {
        if (_source0.is_I8) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      {
        if (_source0.is_I16) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      {
        if (_source0.is_I32) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      {
        if (_source0.is_I64) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      {
        if (_source0.is_I128) {
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
        RAST._IExpr _out0;
        DCOMP._IOwnership _out1;
        (this).FromOwned(r, expectedOwnership, out _out0, out _out1);
        @out = _out0;
        resultingOwnership = _out1;
        return ;
      } else if (object.Equals(ownership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        RAST._IExpr _out2;
        DCOMP._IOwnership _out3;
        (this).FromOwned(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), r, DAST.Format.UnaryOpFormat.create_NoFormat()), expectedOwnership, out _out2, out _out3);
        @out = _out2;
        resultingOwnership = _out3;
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
      DAST._IExpression _source0 = e;
      {
        if (_source0.is_Literal) {
          DAST._ILiteral _h170 = _source0.dtor_Literal_a0;
          if (_h170.is_BoolLiteral) {
            bool _0_b = _h170.dtor_BoolLiteral_a0;
            {
              RAST._IExpr _out0;
              DCOMP._IOwnership _out1;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_0_b), expectedOwnership, out _out0, out _out1);
              r = _out0;
              resultingOwnership = _out1;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_Literal) {
          DAST._ILiteral _h171 = _source0.dtor_Literal_a0;
          if (_h171.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1_i = _h171.dtor_IntLiteral_a0;
            DAST._IType _2_t = _h171.dtor_IntLiteral_a1;
            {
              DAST._IType _source1 = _2_t;
              {
                if (_source1.is_Primitive) {
                  DAST._IPrimitive _h70 = _source1.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    {
                      if ((new BigInteger((_1_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1_i, true, false));
                      }
                    }
                    goto after_match1;
                  }
                }
              }
              {
                DAST._IType _3_o = _source1;
                {
                  RAST._IType _4_genType;
                  RAST._IType _out2;
                  _out2 = (this).GenType(_3_o, DCOMP.GenTypeContext.@default());
                  _4_genType = _out2;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1_i), _4_genType);
                }
              }
            after_match1: ;
              RAST._IExpr _out3;
              DCOMP._IOwnership _out4;
              (this).FromOwned(r, expectedOwnership, out _out3, out _out4);
              r = _out3;
              resultingOwnership = _out4;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_Literal) {
          DAST._ILiteral _h172 = _source0.dtor_Literal_a0;
          if (_h172.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _5_n = _h172.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _6_d = _h172.dtor_DecLiteral_a1;
            DAST._IType _7_t = _h172.dtor_DecLiteral_a2;
            {
              DAST._IType _source2 = _7_t;
              {
                if (_source2.is_Primitive) {
                  DAST._IPrimitive _h71 = _source2.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _5_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _6_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                    goto after_match2;
                  }
                }
              }
              {
                DAST._IType _8_o = _source2;
                {
                  RAST._IType _9_genType;
                  RAST._IType _out5;
                  _out5 = (this).GenType(_8_o, DCOMP.GenTypeContext.@default());
                  _9_genType = _out5;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _5_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _6_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _9_genType);
                }
              }
            after_match2: ;
              RAST._IExpr _out6;
              DCOMP._IOwnership _out7;
              (this).FromOwned(r, expectedOwnership, out _out6, out _out7);
              r = _out6;
              resultingOwnership = _out7;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_Literal) {
          DAST._ILiteral _h173 = _source0.dtor_Literal_a0;
          if (_h173.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _10_l = _h173.dtor_StringLiteral_a0;
            bool _11_verbatim = _h173.dtor_verbatim;
            {
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_10_l, false, _11_verbatim));
              RAST._IExpr _out8;
              DCOMP._IOwnership _out9;
              (this).FromOwned(r, expectedOwnership, out _out8, out _out9);
              r = _out8;
              resultingOwnership = _out9;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_Literal) {
          DAST._ILiteral _h174 = _source0.dtor_Literal_a0;
          if (_h174.is_CharLiteralUTF16) {
            BigInteger _12_c = _h174.dtor_CharLiteralUTF16_a0;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_12_c));
              r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
              RAST._IExpr _out10;
              DCOMP._IOwnership _out11;
              (this).FromOwned(r, expectedOwnership, out _out10, out _out11);
              r = _out10;
              resultingOwnership = _out11;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_Literal) {
          DAST._ILiteral _h175 = _source0.dtor_Literal_a0;
          if (_h175.is_CharLiteral) {
            Dafny.Rune _13_c = _h175.dtor_CharLiteral_a0;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_13_c).Value)));
              if (!((this).UnicodeChars)) {
                r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              } else {
                r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
              RAST._IExpr _out12;
              DCOMP._IOwnership _out13;
              (this).FromOwned(r, expectedOwnership, out _out12, out _out13);
              r = _out12;
              resultingOwnership = _out13;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        DAST._ILiteral _h176 = _source0.dtor_Literal_a0;
        DAST._IType _14_tpe = _h176.dtor_Null_a0;
        {
          RAST._IType _15_tpeGen;
          RAST._IType _out14;
          _out14 = (this).GenType(_14_tpe, DCOMP.GenTypeContext.@default());
          _15_tpeGen = _out14;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null"));
          } else {
            r = RAST.Expr.create_TypeAscription(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _15_tpeGen);
          }
          RAST._IExpr _out15;
          DCOMP._IOwnership _out16;
          (this).FromOwned(r, expectedOwnership, out _out15, out _out16);
          r = _out15;
          resultingOwnership = _out16;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      }
    after_match0: ;
    }
    public void GenExprBinary(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs0 = e;
      DAST._IBinOp _0_op = _let_tmp_rhs0.dtor_op;
      DAST._IExpression _1_lExpr = _let_tmp_rhs0.dtor_left;
      DAST._IExpression _2_rExpr = _let_tmp_rhs0.dtor_right;
      DAST.Format._IBinaryOpFormat _3_format = _let_tmp_rhs0.dtor_format2;
      bool _4_becomesLeftCallsRight;
      DAST._IBinOp _source0 = _0_op;
      {
        bool disjunctiveMatch0 = false;
        if (_source0.is_SetMerge) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_SetSubtraction) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_SetIntersection) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_SetDisjoint) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_MapMerge) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_MapSubtraction) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_MultisetMerge) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_MultisetSubtraction) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_MultisetIntersection) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_MultisetDisjoint) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_Concat) {
          disjunctiveMatch0 = true;
        }
        if (disjunctiveMatch0) {
          _4_becomesLeftCallsRight = true;
          goto after_match0;
        }
      }
      {
        _4_becomesLeftCallsRight = false;
      }
    after_match0: ;
      bool _5_becomesRightCallsLeft;
      DAST._IBinOp _source1 = _0_op;
      {
        if (_source1.is_In) {
          _5_becomesRightCallsLeft = true;
          goto after_match1;
        }
      }
      {
        _5_becomesRightCallsLeft = false;
      }
    after_match1: ;
      bool _6_becomesCallLeftRight;
      DAST._IBinOp _source2 = _0_op;
      {
        if (_source2.is_Eq) {
          bool referential0 = _source2.dtor_referential;
          if ((referential0) == (true)) {
            _6_becomesCallLeftRight = false;
            goto after_match2;
          }
        }
      }
      {
        if (_source2.is_SetMerge) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_SetSubtraction) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_SetIntersection) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_SetDisjoint) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_MapMerge) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_MapSubtraction) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_MultisetMerge) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_MultisetSubtraction) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_MultisetIntersection) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_MultisetDisjoint) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_Concat) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        _6_becomesCallLeftRight = false;
      }
    after_match2: ;
      DCOMP._IOwnership _7_expectedLeftOwnership;
      if (_4_becomesLeftCallsRight) {
        _7_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipAutoBorrowed();
      } else if ((_5_becomesRightCallsLeft) || (_6_becomesCallLeftRight)) {
        _7_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        _7_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipOwned();
      }
      DCOMP._IOwnership _8_expectedRightOwnership;
      if ((_4_becomesLeftCallsRight) || (_6_becomesCallLeftRight)) {
        _8_expectedRightOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else if (_5_becomesRightCallsLeft) {
        _8_expectedRightOwnership = DCOMP.Ownership.create_OwnershipAutoBorrowed();
      } else {
        _8_expectedRightOwnership = DCOMP.Ownership.create_OwnershipOwned();
      }
      RAST._IExpr _9_left;
      DCOMP._IOwnership _10___v112;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _11_recIdentsL;
      RAST._IExpr _out0;
      DCOMP._IOwnership _out1;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2;
      (this).GenExpr(_1_lExpr, selfIdent, env, _7_expectedLeftOwnership, out _out0, out _out1, out _out2);
      _9_left = _out0;
      _10___v112 = _out1;
      _11_recIdentsL = _out2;
      RAST._IExpr _12_right;
      DCOMP._IOwnership _13___v113;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _14_recIdentsR;
      RAST._IExpr _out3;
      DCOMP._IOwnership _out4;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out5;
      (this).GenExpr(_2_rExpr, selfIdent, env, _8_expectedRightOwnership, out _out3, out _out4, out _out5);
      _12_right = _out3;
      _13___v113 = _out4;
      _14_recIdentsR = _out5;
      DAST._IBinOp _source3 = _0_op;
      {
        if (_source3.is_In) {
          {
            r = ((_12_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_9_left);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_SeqProperPrefix) {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _9_left, _12_right, _3_format);
          goto after_match3;
        }
      }
      {
        if (_source3.is_SeqPrefix) {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _9_left, _12_right, _3_format);
          goto after_match3;
        }
      }
      {
        if (_source3.is_SetMerge) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_SetSubtraction) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_SetIntersection) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_Subset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _9_left, _12_right, _3_format);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_ProperSubset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _9_left, _12_right, _3_format);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_SetDisjoint) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_MapMerge) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_MapSubtraction) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_MultisetMerge) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_MultisetSubtraction) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_MultisetIntersection) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_Submultiset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _9_left, _12_right, _3_format);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_ProperSubmultiset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _9_left, _12_right, _3_format);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_MultisetDisjoint) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_Concat) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        {
          if ((DCOMP.COMP.OpTable).Contains(_0_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_0_op), _9_left, _12_right, _3_format);
          } else {
            DAST._IBinOp _source4 = _0_op;
            {
              if (_source4.is_Eq) {
                bool _15_referential = _source4.dtor_referential;
                {
                  if (_15_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _9_left, _12_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_2_rExpr).is_SeqValue) && ((new BigInteger(((_2_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1_lExpr).is_SeqValue) && ((new BigInteger(((_1_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_12_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _9_left, _12_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
                goto after_match4;
              }
            }
            {
              if (_source4.is_EuclidianDiv) {
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_9_left, _12_right));
                }
                goto after_match4;
              }
            }
            {
              if (_source4.is_EuclidianMod) {
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_9_left, _12_right));
                }
                goto after_match4;
              }
            }
            {
              Dafny.ISequence<Dafny.Rune> _16_op = _source4.dtor_Passthrough_a0;
              {
                r = RAST.Expr.create_BinaryOp(_16_op, _9_left, _12_right, _3_format);
              }
            }
          after_match4: ;
          }
        }
      }
    after_match3: ;
      RAST._IExpr _out6;
      DCOMP._IOwnership _out7;
      (this).FromOwned(r, expectedOwnership, out _out6, out _out7);
      r = _out6;
      resultingOwnership = _out7;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_11_recIdentsL, _14_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs0 = e;
      DAST._IExpression _0_expr = _let_tmp_rhs0.dtor_value;
      DAST._IType _1_fromTpe = _let_tmp_rhs0.dtor_from;
      DAST._IType _2_toTpe = _let_tmp_rhs0.dtor_typ;
      DAST._IType _let_tmp_rhs1 = _2_toTpe;
      DAST._IResolvedType _let_tmp_rhs2 = _let_tmp_rhs1.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3_path = _let_tmp_rhs2.dtor_path;
      Dafny.ISequence<DAST._IType> _4_typeArgs = _let_tmp_rhs2.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs3 = _let_tmp_rhs2.dtor_kind;
      DAST._IType _5_b = _let_tmp_rhs3.dtor_baseType;
      DAST._INewtypeRange _6_range = _let_tmp_rhs3.dtor_range;
      bool _7_erase = _let_tmp_rhs3.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _8___v115 = _let_tmp_rhs2.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _9___v116 = _let_tmp_rhs2.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _10___v117 = _let_tmp_rhs2.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _11_nativeToType;
      _11_nativeToType = DCOMP.COMP.NewtypeToRustType(_5_b, _6_range);
      if (object.Equals(_1_fromTpe, _5_b)) {
        RAST._IExpr _12_recursiveGen;
        DCOMP._IOwnership _13_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _14_recIdents;
        RAST._IExpr _out0;
        DCOMP._IOwnership _out1;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2;
        (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out0, out _out1, out _out2);
        _12_recursiveGen = _out0;
        _13_recOwned = _out1;
        _14_recIdents = _out2;
        readIdents = _14_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source0 = _11_nativeToType;
        {
          if (_source0.is_Some) {
            RAST._IType _15_v = _source0.dtor_value;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_12_recursiveGen, RAST.Expr.create_ExprFromType(_15_v)));
            RAST._IExpr _out3;
            DCOMP._IOwnership _out4;
            (this).FromOwned(r, expectedOwnership, out _out3, out _out4);
            r = _out3;
            resultingOwnership = _out4;
            goto after_match0;
          }
        }
        {
          if (_7_erase) {
            r = _12_recursiveGen;
          } else {
            RAST._IType _16_rhsType;
            RAST._IType _out5;
            _out5 = (this).GenType(_2_toTpe, DCOMP.GenTypeContext.InBinding());
            _16_rhsType = _out5;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_16_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_12_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out6;
          DCOMP._IOwnership _out7;
          (this).FromOwnership(r, _13_recOwned, expectedOwnership, out _out6, out _out7);
          r = _out6;
          resultingOwnership = _out7;
        }
      after_match0: ;
      } else {
        if ((_11_nativeToType).is_Some) {
          DAST._IType _source1 = _1_fromTpe;
          {
            if (_source1.is_UserDefined) {
              DAST._IResolvedType resolved0 = _source1.dtor_resolved;
              DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
              if (kind0.is_Newtype) {
                DAST._IType _17_b0 = kind0.dtor_baseType;
                DAST._INewtypeRange _18_range0 = kind0.dtor_range;
                bool _19_erase0 = kind0.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _20_attributes0 = resolved0.dtor_attributes;
                {
                  Std.Wrappers._IOption<RAST._IType> _21_nativeFromType;
                  _21_nativeFromType = DCOMP.COMP.NewtypeToRustType(_17_b0, _18_range0);
                  if ((_21_nativeFromType).is_Some) {
                    RAST._IExpr _22_recursiveGen;
                    DCOMP._IOwnership _23_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _24_recIdents;
                    RAST._IExpr _out8;
                    DCOMP._IOwnership _out9;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out10;
                    (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out8, out _out9, out _out10);
                    _22_recursiveGen = _out8;
                    _23_recOwned = _out9;
                    _24_recIdents = _out10;
                    RAST._IExpr _out11;
                    DCOMP._IOwnership _out12;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_22_recursiveGen, (_11_nativeToType).dtor_value), _23_recOwned, expectedOwnership, out _out11, out _out12);
                    r = _out11;
                    resultingOwnership = _out12;
                    readIdents = _24_recIdents;
                    return ;
                  }
                }
                goto after_match1;
              }
            }
          }
          {
          }
        after_match1: ;
          if (object.Equals(_1_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _25_recursiveGen;
            DCOMP._IOwnership _26_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _27_recIdents;
            RAST._IExpr _out13;
            DCOMP._IOwnership _out14;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out15;
            (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out13, out _out14, out _out15);
            _25_recursiveGen = _out13;
            _26_recOwned = _out14;
            _27_recIdents = _out15;
            RAST._IExpr _out16;
            DCOMP._IOwnership _out17;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_25_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_11_nativeToType).dtor_value), _26_recOwned, expectedOwnership, out _out16, out _out17);
            r = _out16;
            resultingOwnership = _out17;
            readIdents = _27_recIdents;
            return ;
          }
        }
        RAST._IExpr _out18;
        DCOMP._IOwnership _out19;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out20;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_0_expr, _1_fromTpe, _5_b), _5_b, _2_toTpe), selfIdent, env, expectedOwnership, out _out18, out _out19, out _out20);
        r = _out18;
        resultingOwnership = _out19;
        readIdents = _out20;
      }
    }
    public void GenExprConvertFromNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs0 = e;
      DAST._IExpression _0_expr = _let_tmp_rhs0.dtor_value;
      DAST._IType _1_fromTpe = _let_tmp_rhs0.dtor_from;
      DAST._IType _2_toTpe = _let_tmp_rhs0.dtor_typ;
      DAST._IType _let_tmp_rhs1 = _1_fromTpe;
      DAST._IResolvedType _let_tmp_rhs2 = _let_tmp_rhs1.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3___v123 = _let_tmp_rhs2.dtor_path;
      Dafny.ISequence<DAST._IType> _4___v124 = _let_tmp_rhs2.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs3 = _let_tmp_rhs2.dtor_kind;
      DAST._IType _5_b = _let_tmp_rhs3.dtor_baseType;
      DAST._INewtypeRange _6_range = _let_tmp_rhs3.dtor_range;
      bool _7_erase = _let_tmp_rhs3.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _8_attributes = _let_tmp_rhs2.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _9___v125 = _let_tmp_rhs2.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _10___v126 = _let_tmp_rhs2.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _11_nativeFromType;
      _11_nativeFromType = DCOMP.COMP.NewtypeToRustType(_5_b, _6_range);
      if (object.Equals(_5_b, _2_toTpe)) {
        RAST._IExpr _12_recursiveGen;
        DCOMP._IOwnership _13_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _14_recIdents;
        RAST._IExpr _out0;
        DCOMP._IOwnership _out1;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2;
        (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out0, out _out1, out _out2);
        _12_recursiveGen = _out0;
        _13_recOwned = _out1;
        _14_recIdents = _out2;
        readIdents = _14_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source0 = _11_nativeFromType;
        {
          if (_source0.is_Some) {
            RAST._IType _15_v = _source0.dtor_value;
            RAST._IType _16_toTpeRust;
            RAST._IType _out3;
            _out3 = (this).GenType(_2_toTpe, DCOMP.GenTypeContext.@default());
            _16_toTpeRust = _out3;
            r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_16_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_12_recursiveGen));
            RAST._IExpr _out4;
            DCOMP._IOwnership _out5;
            (this).FromOwned(r, expectedOwnership, out _out4, out _out5);
            r = _out4;
            resultingOwnership = _out5;
            goto after_match0;
          }
        }
        {
          if (_7_erase) {
            r = _12_recursiveGen;
          } else {
            r = (_12_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out6;
          DCOMP._IOwnership _out7;
          (this).FromOwnership(r, _13_recOwned, expectedOwnership, out _out6, out _out7);
          r = _out6;
          resultingOwnership = _out7;
        }
      after_match0: ;
      } else {
        if ((_11_nativeFromType).is_Some) {
          if (object.Equals(_2_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _17_recursiveGen;
            DCOMP._IOwnership _18_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _19_recIdents;
            RAST._IExpr _out8;
            DCOMP._IOwnership _out9;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out10;
            (this).GenExpr(_0_expr, selfIdent, env, expectedOwnership, out _out8, out _out9, out _out10);
            _17_recursiveGen = _out8;
            _18_recOwned = _out9;
            _19_recIdents = _out10;
            RAST._IExpr _out11;
            DCOMP._IOwnership _out12;
            (this).FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_17_recursiveGen, (this).DafnyCharUnderlying)), _18_recOwned, expectedOwnership, out _out11, out _out12);
            r = _out11;
            resultingOwnership = _out12;
            readIdents = _19_recIdents;
            return ;
          }
        }
        RAST._IExpr _out13;
        DCOMP._IOwnership _out14;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out15;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_0_expr, _1_fromTpe, _5_b), _5_b, _2_toTpe), selfIdent, env, expectedOwnership, out _out13, out _out14, out _out15);
        r = _out13;
        resultingOwnership = _out14;
        readIdents = _out15;
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
        Std.Wrappers._IResult<__T, __E> _0_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_0_valueOrError0).IsFailure()) {
          return (_0_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1_head = (_0_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _2_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_2_valueOrError1).IsFailure()) {
            return (_2_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _3_tail = (_2_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1_head), _3_tail));
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
          RAST._IType _0_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          RAST._IType _1_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel((this).upcast)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_0_fromTpeUnderlying, _1_toTpeUnderlying))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _2_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_2_valueOrError0).IsFailure()) {
          return (_2_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _3_lambda = (_2_valueOrError0).Extract();
          if ((fromType).is_Arrow) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(_3_lambda);
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).Apply1(_3_lambda));
          }
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _4_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim12 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr12 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
          for (int i12 = 0; i12 < dim12; i12++) {
            var _5_i = (BigInteger) i12;
            arr12[(int)(_5_i)] = (this).UpcastConversionLambda((((fromType).dtor_resolved).dtor_typeArgs).Select(_5_i), ((fromTpe).dtor_arguments).Select(_5_i), (((toType).dtor_resolved).dtor_typeArgs).Select(_5_i), ((toTpe).dtor_arguments).Select(_5_i), typeParams);
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr12);
        }))());
        if ((_4_valueOrError1).IsFailure()) {
          return (_4_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _6_lambdas = (_4_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim13 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr13 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim13, "array size exceeds memory limit")];
  for (int i13 = 0; i13 < dim13; i13++) {
    var _7_i = (BigInteger) i13;
    arr13[(int)(_7_i)] = ((fromTpe).dtor_arguments).Select(_7_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr13);
}))())).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_6_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _8_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _9_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _10_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _11_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _12_valueOrError2 = (this).UpcastConversionLambda(_10_newFromType, _8_newFromTpe, _11_newToType, _9_newToTpe, typeParams);
        if ((_12_valueOrError2).IsFailure()) {
          return (_12_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _13_coerceArg = (_12_valueOrError2).Extract();
          RAST._IExpr _14_collectionType = (RAST.__default.dafny__runtime).MSel(((fromTpe).dtor_baseName).dtor_name);
          RAST._IExpr _15_baseType = (((((fromTpe).dtor_baseName).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? ((_14_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((fromTpe).dtor_arguments).Select(BigInteger.Zero), _8_newFromTpe))) : ((_14_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_8_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_15_baseType).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_13_coerceArg));
        }
      } else if ((((((((((fromTpe).is_DynType) && (((fromTpe).dtor_underlying).is_FnType)) && ((toTpe).is_DynType)) && (((toTpe).dtor_underlying).is_FnType)) && ((((fromTpe).dtor_underlying).dtor_arguments).Equals(((toTpe).dtor_underlying).dtor_arguments))) && ((fromType).is_Arrow)) && ((toType).is_Arrow)) && ((new BigInteger((((fromTpe).dtor_underlying).dtor_arguments).Count)) == (BigInteger.One))) && (((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).is_Borrowed)) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _16_valueOrError3 = (this).UpcastConversionLambda((fromType).dtor_result, ((fromTpe).dtor_underlying).dtor_returnType, (toType).dtor_result, ((toTpe).dtor_underlying).dtor_returnType, typeParams);
        if ((_16_valueOrError3).IsFailure()) {
          return (_16_valueOrError3).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _17_lambda = (_16_valueOrError3).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn1_coerce"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying, ((fromTpe).dtor_underlying).dtor_returnType, ((toTpe).dtor_underlying).dtor_returnType))).Apply1(_17_lambda));
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
      DAST._IExpression _let_tmp_rhs0 = e;
      DAST._IExpression _0_expr = _let_tmp_rhs0.dtor_value;
      DAST._IType _1_fromTpe = _let_tmp_rhs0.dtor_from;
      DAST._IType _2_toTpe = _let_tmp_rhs0.dtor_typ;
      RAST._IType _3_fromTpeGen;
      RAST._IType _out0;
      _out0 = (this).GenType(_1_fromTpe, DCOMP.GenTypeContext.InBinding());
      _3_fromTpeGen = _out0;
      RAST._IType _4_toTpeGen;
      RAST._IType _out1;
      _out1 = (this).GenType(_2_toTpe, DCOMP.GenTypeContext.InBinding());
      _4_toTpeGen = _out1;
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _5_upcastConverter;
      _5_upcastConverter = (this).UpcastConversionLambda(_1_fromTpe, _3_fromTpeGen, _2_toTpe, _4_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_5_upcastConverter).is_Success) {
        RAST._IExpr _6_conversionLambda;
        _6_conversionLambda = (_5_upcastConverter).dtor_value;
        RAST._IExpr _7_recursiveGen;
        DCOMP._IOwnership _8_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _9_recIdents;
        RAST._IExpr _out2;
        DCOMP._IOwnership _out3;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out4;
        (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out2, out _out3, out _out4);
        _7_recursiveGen = _out2;
        _8_recOwned = _out3;
        _9_recIdents = _out4;
        readIdents = _9_recIdents;
        r = (_6_conversionLambda).Apply1(_7_recursiveGen);
        RAST._IExpr _out5;
        DCOMP._IOwnership _out6;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out5, out _out6);
        r = _out5;
        resultingOwnership = _out6;
      } else if ((this).IsDowncastConversion(_3_fromTpeGen, _4_toTpeGen)) {
        RAST._IExpr _10_recursiveGen;
        DCOMP._IOwnership _11_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _12_recIdents;
        RAST._IExpr _out7;
        DCOMP._IOwnership _out8;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out9;
        (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out7, out _out8, out _out9);
        _10_recursiveGen = _out7;
        _11_recOwned = _out8;
        _12_recIdents = _out9;
        readIdents = _12_recIdents;
        _4_toTpeGen = (_4_toTpeGen).ObjectOrPointerUnderlying();
        r = ((RAST.__default.dafny__runtime).MSel((this).downcast)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_10_recursiveGen, RAST.Expr.create_ExprFromType(_4_toTpeGen)));
        RAST._IExpr _out10;
        DCOMP._IOwnership _out11;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out10, out _out11);
        r = _out10;
        resultingOwnership = _out11;
      } else {
        RAST._IExpr _13_recursiveGen;
        DCOMP._IOwnership _14_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _15_recIdents;
        RAST._IExpr _out12;
        DCOMP._IOwnership _out13;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out14;
        (this).GenExpr(_0_expr, selfIdent, env, expectedOwnership, out _out12, out _out13, out _out14);
        _13_recursiveGen = _out12;
        _14_recOwned = _out13;
        _15_recIdents = _out14;
        readIdents = _15_recIdents;
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _let_tmp_rhs1 = _5_upcastConverter;
        _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>> _let_tmp_rhs2 = _let_tmp_rhs1.dtor_error;
        DAST._IType _16_fromType = _let_tmp_rhs2.dtor__0;
        RAST._IType _17_fromTpeGen = _let_tmp_rhs2.dtor__1;
        DAST._IType _18_toType = _let_tmp_rhs2.dtor__2;
        RAST._IType _19_toTpeGen = _let_tmp_rhs2.dtor__3;
        Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _20_m = _let_tmp_rhs2.dtor__4;
        Dafny.ISequence<Dafny.Rune> _21_msg;
        _21_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_17_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_19_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_21_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_13_recursiveGen)._ToString(DCOMP.__default.IND), _21_msg));
        RAST._IExpr _out15;
        DCOMP._IOwnership _out16;
        (this).FromOwnership(r, _14_recOwned, expectedOwnership, out _out15, out _out16);
        r = _out15;
        resultingOwnership = _out16;
      }
    }
    public void GenExprConvert(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs0 = e;
      DAST._IExpression _0_expr = _let_tmp_rhs0.dtor_value;
      DAST._IType _1_fromTpe = _let_tmp_rhs0.dtor_from;
      DAST._IType _2_toTpe = _let_tmp_rhs0.dtor_typ;
      if (object.Equals(_1_fromTpe, _2_toTpe)) {
        RAST._IExpr _3_recursiveGen;
        DCOMP._IOwnership _4_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5_recIdents;
        RAST._IExpr _out0;
        DCOMP._IOwnership _out1;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2;
        (this).GenExpr(_0_expr, selfIdent, env, expectedOwnership, out _out0, out _out1, out _out2);
        _3_recursiveGen = _out0;
        _4_recOwned = _out1;
        _5_recIdents = _out2;
        r = _3_recursiveGen;
        RAST._IExpr _out3;
        DCOMP._IOwnership _out4;
        (this).FromOwnership(r, _4_recOwned, expectedOwnership, out _out3, out _out4);
        r = _out3;
        resultingOwnership = _out4;
        readIdents = _5_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source0 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1_fromTpe, _2_toTpe);
        {
          DAST._IType _10 = _source0.dtor__1;
          if (_10.is_UserDefined) {
            DAST._IResolvedType resolved0 = _10.dtor_resolved;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Newtype) {
              DAST._IType _6_b = kind0.dtor_baseType;
              DAST._INewtypeRange _7_range = kind0.dtor_range;
              bool _8_erase = kind0.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _9_attributes = resolved0.dtor_attributes;
              {
                RAST._IExpr _out5;
                DCOMP._IOwnership _out6;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out7;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out5, out _out6, out _out7);
                r = _out5;
                resultingOwnership = _out6;
                readIdents = _out7;
              }
              goto after_match0;
            }
          }
        }
        {
          DAST._IType _00 = _source0.dtor__0;
          if (_00.is_UserDefined) {
            DAST._IResolvedType resolved1 = _00.dtor_resolved;
            DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
            if (kind1.is_Newtype) {
              DAST._IType _10_b = kind1.dtor_baseType;
              DAST._INewtypeRange _11_range = kind1.dtor_range;
              bool _12_erase = kind1.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _13_attributes = resolved1.dtor_attributes;
              {
                RAST._IExpr _out8;
                DCOMP._IOwnership _out9;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out10;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out8, out _out9, out _out10);
                r = _out8;
                resultingOwnership = _out9;
                readIdents = _out10;
              }
              goto after_match0;
            }
          }
        }
        {
          DAST._IType _01 = _source0.dtor__0;
          if (_01.is_Primitive) {
            DAST._IPrimitive _h70 = _01.dtor_Primitive_a0;
            if (_h70.is_Int) {
              DAST._IType _11 = _source0.dtor__1;
              if (_11.is_Primitive) {
                DAST._IPrimitive _h71 = _11.dtor_Primitive_a0;
                if (_h71.is_Real) {
                  {
                    RAST._IExpr _14_recursiveGen;
                    DCOMP._IOwnership _15___v137;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _16_recIdents;
                    RAST._IExpr _out11;
                    DCOMP._IOwnership _out12;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out13;
                    (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out11, out _out12, out _out13);
                    _14_recursiveGen = _out11;
                    _15___v137 = _out12;
                    _16_recIdents = _out13;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_14_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out14;
                    DCOMP._IOwnership _out15;
                    (this).FromOwned(r, expectedOwnership, out _out14, out _out15);
                    r = _out14;
                    resultingOwnership = _out15;
                    readIdents = _16_recIdents;
                  }
                  goto after_match0;
                }
              }
            }
          }
        }
        {
          DAST._IType _02 = _source0.dtor__0;
          if (_02.is_Primitive) {
            DAST._IPrimitive _h72 = _02.dtor_Primitive_a0;
            if (_h72.is_Real) {
              DAST._IType _12 = _source0.dtor__1;
              if (_12.is_Primitive) {
                DAST._IPrimitive _h73 = _12.dtor_Primitive_a0;
                if (_h73.is_Int) {
                  {
                    RAST._IExpr _17_recursiveGen;
                    DCOMP._IOwnership _18___v138;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _19_recIdents;
                    RAST._IExpr _out16;
                    DCOMP._IOwnership _out17;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out18;
                    (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out16, out _out17, out _out18);
                    _17_recursiveGen = _out16;
                    _18___v138 = _out17;
                    _19_recIdents = _out18;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_17_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out19;
                    DCOMP._IOwnership _out20;
                    (this).FromOwned(r, expectedOwnership, out _out19, out _out20);
                    r = _out19;
                    resultingOwnership = _out20;
                    readIdents = _19_recIdents;
                  }
                  goto after_match0;
                }
              }
            }
          }
        }
        {
          DAST._IType _03 = _source0.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h74 = _03.dtor_Primitive_a0;
            if (_h74.is_Int) {
              DAST._IType _13 = _source0.dtor__1;
              if (_13.is_Passthrough) {
                {
                  RAST._IType _20_rhsType;
                  RAST._IType _out21;
                  _out21 = (this).GenType(_2_toTpe, DCOMP.GenTypeContext.InBinding());
                  _20_rhsType = _out21;
                  RAST._IExpr _21_recursiveGen;
                  DCOMP._IOwnership _22___v140;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _23_recIdents;
                  RAST._IExpr _out22;
                  DCOMP._IOwnership _out23;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out24;
                  (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out22, out _out23, out _out24);
                  _21_recursiveGen = _out22;
                  _22___v140 = _out23;
                  _23_recIdents = _out24;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_20_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_21_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out25;
                  DCOMP._IOwnership _out26;
                  (this).FromOwned(r, expectedOwnership, out _out25, out _out26);
                  r = _out25;
                  resultingOwnership = _out26;
                  readIdents = _23_recIdents;
                }
                goto after_match0;
              }
            }
          }
        }
        {
          DAST._IType _04 = _source0.dtor__0;
          if (_04.is_Passthrough) {
            DAST._IType _14 = _source0.dtor__1;
            if (_14.is_Primitive) {
              DAST._IPrimitive _h75 = _14.dtor_Primitive_a0;
              if (_h75.is_Int) {
                {
                  RAST._IType _24_rhsType;
                  RAST._IType _out27;
                  _out27 = (this).GenType(_1_fromTpe, DCOMP.GenTypeContext.InBinding());
                  _24_rhsType = _out27;
                  RAST._IExpr _25_recursiveGen;
                  DCOMP._IOwnership _26___v142;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _27_recIdents;
                  RAST._IExpr _out28;
                  DCOMP._IOwnership _out29;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out30;
                  (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out28, out _out29, out _out30);
                  _25_recursiveGen = _out28;
                  _26___v142 = _out29;
                  _27_recIdents = _out30;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_25_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out31;
                  DCOMP._IOwnership _out32;
                  (this).FromOwned(r, expectedOwnership, out _out31, out _out32);
                  r = _out31;
                  resultingOwnership = _out32;
                  readIdents = _27_recIdents;
                }
                goto after_match0;
              }
            }
          }
        }
        {
          DAST._IType _05 = _source0.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h76 = _05.dtor_Primitive_a0;
            if (_h76.is_Int) {
              DAST._IType _15 = _source0.dtor__1;
              if (_15.is_Primitive) {
                DAST._IPrimitive _h77 = _15.dtor_Primitive_a0;
                if (_h77.is_Char) {
                  {
                    RAST._IType _28_rhsType;
                    RAST._IType _out33;
                    _out33 = (this).GenType(_2_toTpe, DCOMP.GenTypeContext.InBinding());
                    _28_rhsType = _out33;
                    RAST._IExpr _29_recursiveGen;
                    DCOMP._IOwnership _30___v143;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _31_recIdents;
                    RAST._IExpr _out34;
                    DCOMP._IOwnership _out35;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out36;
                    (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out34, out _out35, out _out36);
                    _29_recursiveGen = _out34;
                    _30___v143 = _out35;
                    _31_recIdents = _out36;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_29_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out37;
                    DCOMP._IOwnership _out38;
                    (this).FromOwned(r, expectedOwnership, out _out37, out _out38);
                    r = _out37;
                    resultingOwnership = _out38;
                    readIdents = _31_recIdents;
                  }
                  goto after_match0;
                }
              }
            }
          }
        }
        {
          DAST._IType _06 = _source0.dtor__0;
          if (_06.is_Primitive) {
            DAST._IPrimitive _h78 = _06.dtor_Primitive_a0;
            if (_h78.is_Char) {
              DAST._IType _16 = _source0.dtor__1;
              if (_16.is_Primitive) {
                DAST._IPrimitive _h79 = _16.dtor_Primitive_a0;
                if (_h79.is_Int) {
                  {
                    RAST._IType _32_rhsType;
                    RAST._IType _out39;
                    _out39 = (this).GenType(_1_fromTpe, DCOMP.GenTypeContext.InBinding());
                    _32_rhsType = _out39;
                    RAST._IExpr _33_recursiveGen;
                    DCOMP._IOwnership _34___v144;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _35_recIdents;
                    RAST._IExpr _out40;
                    DCOMP._IOwnership _out41;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out42;
                    (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out40, out _out41, out _out42);
                    _33_recursiveGen = _out40;
                    _34___v144 = _out41;
                    _35_recIdents = _out42;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_33_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out43;
                    DCOMP._IOwnership _out44;
                    (this).FromOwned(r, expectedOwnership, out _out43, out _out44);
                    r = _out43;
                    resultingOwnership = _out44;
                    readIdents = _35_recIdents;
                  }
                  goto after_match0;
                }
              }
            }
          }
        }
        {
          DAST._IType _07 = _source0.dtor__0;
          if (_07.is_Passthrough) {
            DAST._IType _17 = _source0.dtor__1;
            if (_17.is_Passthrough) {
              {
                RAST._IExpr _36_recursiveGen;
                DCOMP._IOwnership _37___v147;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _38_recIdents;
                RAST._IExpr _out45;
                DCOMP._IOwnership _out46;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out47;
                (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out45, out _out46, out _out47);
                _36_recursiveGen = _out45;
                _37___v147 = _out46;
                _38_recIdents = _out47;
                RAST._IType _39_toTpeGen;
                RAST._IType _out48;
                _out48 = (this).GenType(_2_toTpe, DCOMP.GenTypeContext.InBinding());
                _39_toTpeGen = _out48;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_36_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_39_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out49;
                DCOMP._IOwnership _out50;
                (this).FromOwned(r, expectedOwnership, out _out49, out _out50);
                r = _out49;
                resultingOwnership = _out50;
                readIdents = _38_recIdents;
              }
              goto after_match0;
            }
          }
        }
        {
          {
            RAST._IExpr _out51;
            DCOMP._IOwnership _out52;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out53;
            (this).GenExprConvertOther(e, selfIdent, env, expectedOwnership, out _out51, out _out52, out _out53);
            r = _out51;
            resultingOwnership = _out52;
            readIdents = _out53;
          }
        }
      after_match0: ;
      }
      return ;
    }
    public void GenIdent(Dafny.ISequence<Dafny.Rune> rName, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      r = RAST.Expr.create_Identifier(rName);
      Std.Wrappers._IOption<RAST._IType> _0_tpe;
      _0_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1_placeboOpt;
      if ((_0_tpe).is_Some) {
        _1_placeboOpt = ((_0_tpe).dtor_value).ExtractMaybePlacebo();
      } else {
        _1_placeboOpt = Std.Wrappers.Option<RAST._IType>.create_None();
      }
      bool _2_currentlyBorrowed;
      _2_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _3_noNeedOfClone;
      _3_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _2_currentlyBorrowed = false;
        _3_noNeedOfClone = true;
        _0_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_1_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        if (_2_currentlyBorrowed) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        } else {
          resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
        }
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_0_tpe).is_Some) && (((_0_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _4_needObjectFromRef;
        _4_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source0 = (selfIdent).dtor_dafnyType;
          {
            if (_source0.is_UserDefined) {
              DAST._IResolvedType resolved0 = _source0.dtor_resolved;
              DAST._IResolvedTypeBase _5_base = resolved0.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _6_attributes = resolved0.dtor_attributes;
              return ((_5_base).is_Class) || ((_5_base).is_Trait);
            }
          }
          {
            return false;
          }
        }))());
        if (_4_needObjectFromRef) {
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_3_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_3_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_2_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_0_tpe).is_Some) && (((_0_tpe).dtor_value).IsPointer())) {
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
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_0_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_0_attributes).UniqueElements, false, (((_exists_var_0) => {
        DAST._IAttribute _1_attribute = (DAST._IAttribute)_exists_var_0;
        return ((_0_attributes).Contains(_1_attribute)) && ((((_1_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_1_attribute).dtor_args).Count)) == (new BigInteger(2))));
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
      BigInteger _hi0 = new BigInteger((args).Count);
      for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
        DCOMP._IOwnership _1_argOwnership;
        _1_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if (((name).is_CallName) && ((_0_i) < (new BigInteger((((name).dtor_signature)).Count)))) {
          RAST._IType _2_tpe;
          RAST._IType _out0;
          _out0 = (this).GenType(((((name).dtor_signature)).Select(_0_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _2_tpe = _out0;
          if ((_2_tpe).CanReadWithoutClone()) {
            _1_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _3_argExpr;
        DCOMP._IOwnership _4___v154;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5_argIdents;
        RAST._IExpr _out1;
        DCOMP._IOwnership _out2;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out3;
        (this).GenExpr((args).Select(_0_i), selfIdent, env, _1_argOwnership, out _out1, out _out2, out _out3);
        _3_argExpr = _out1;
        _4___v154 = _out2;
        _5_argIdents = _out3;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_3_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _5_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi1 = new BigInteger((typeArgs).Count);
      for (BigInteger _6_typeI = BigInteger.Zero; _6_typeI < _hi1; _6_typeI++) {
        RAST._IType _7_typeExpr;
        RAST._IType _out4;
        _out4 = (this).GenType((typeArgs).Select(_6_typeI), DCOMP.GenTypeContext.@default());
        _7_typeExpr = _out4;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_7_typeExpr));
      }
      DAST._ICallName _source0 = name;
      {
        if (_source0.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _8_nameIdent = _source0.dtor_name;
          Std.Wrappers._IOption<DAST._IType> onType0 = _source0.dtor_onType;
          if (onType0.is_Some) {
            DAST._IType value0 = onType0.dtor_value;
            if (value0.is_UserDefined) {
              DAST._IResolvedType _9_resolvedType = value0.dtor_resolved;
              if ((((_9_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_10_resolvedType, _11_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(((_10_resolvedType).dtor_properMethods).UniqueElements, true, (((_forall_var_0) => {
                Dafny.ISequence<Dafny.Rune> _12_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_0;
                return !(((_10_resolvedType).dtor_properMethods).Contains(_12_m)) || (!object.Equals((_12_m), _11_nameIdent));
              }))))(_9_resolvedType, _8_nameIdent))) {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_9_resolvedType, (_8_nameIdent)), _9_resolvedType));
              } else {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
              }
              goto after_match0;
            }
          }
        }
      }
      {
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
    after_match0: ;
      if ((((((fullNameQualifier).is_Some) && ((selfIdent).is_ThisTyped)) && (((selfIdent).dtor_dafnyType).is_UserDefined)) && ((this).IsSameResolvedType(((selfIdent).dtor_dafnyType).dtor_resolved, (fullNameQualifier).dtor_value))) && (!((this).HasExternAttributeRenamingModule(((fullNameQualifier).dtor_value).dtor_attributes)))) {
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
    }
    public void GenExpr(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source0 = e;
      {
        if (_source0.is_Literal) {
          RAST._IExpr _out0;
          DCOMP._IOwnership _out1;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out0, out _out1, out _out2);
          r = _out0;
          resultingOwnership = _out1;
          readIdents = _out2;
          goto after_match0;
        }
      }
      {
        if (_source0.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _0_name = _source0.dtor_name;
          {
            RAST._IExpr _out3;
            DCOMP._IOwnership _out4;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out5;
            (this).GenIdent(DCOMP.__default.escapeName(_0_name), selfIdent, env, expectedOwnership, out _out3, out _out4, out _out5);
            r = _out3;
            resultingOwnership = _out4;
            readIdents = _out5;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1_path = _source0.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _2_typeArgs = _source0.dtor_typeArgs;
          {
            RAST._IExpr _out6;
            _out6 = DCOMP.COMP.GenPathExpr(_1_path);
            r = _out6;
            if ((new BigInteger((_2_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _3_typeExprs;
              _3_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi0 = new BigInteger((_2_typeArgs).Count);
              for (BigInteger _4_i = BigInteger.Zero; _4_i < _hi0; _4_i++) {
                RAST._IType _5_typeExpr;
                RAST._IType _out7;
                _out7 = (this).GenType((_2_typeArgs).Select(_4_i), DCOMP.GenTypeContext.@default());
                _5_typeExpr = _out7;
                _3_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_3_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_5_typeExpr));
              }
              r = (r).ApplyType(_3_typeExprs);
            }
            if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else {
              RAST._IExpr _out8;
              DCOMP._IOwnership _out9;
              (this).FromOwned(r, expectedOwnership, out _out8, out _out9);
              r = _out8;
              resultingOwnership = _out9;
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_InitializationValue) {
          DAST._IType _6_typ = _source0.dtor_typ;
          {
            RAST._IType _7_typExpr;
            RAST._IType _out10;
            _out10 = (this).GenType(_6_typ, DCOMP.GenTypeContext.@default());
            _7_typExpr = _out10;
            if ((_7_typExpr).IsObjectOrPointer()) {
              r = (_7_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_7_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
            }
            RAST._IExpr _out11;
            DCOMP._IOwnership _out12;
            (this).FromOwned(r, expectedOwnership, out _out11, out _out12);
            r = _out11;
            resultingOwnership = _out12;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _8_values = _source0.dtor_Tuple_a0;
          {
            Dafny.ISequence<RAST._IExpr> _9_exprs;
            _9_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi1 = new BigInteger((_8_values).Count);
            for (BigInteger _10_i = BigInteger.Zero; _10_i < _hi1; _10_i++) {
              RAST._IExpr _11_recursiveGen;
              DCOMP._IOwnership _12___v159;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _13_recIdents;
              RAST._IExpr _out13;
              DCOMP._IOwnership _out14;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out15;
              (this).GenExpr((_8_values).Select(_10_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out13, out _out14, out _out15);
              _11_recursiveGen = _out13;
              _12___v159 = _out14;
              _13_recIdents = _out15;
              _9_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_9_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_11_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _13_recIdents);
            }
            if ((new BigInteger((_8_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) {
              r = RAST.Expr.create_Tuple(_9_exprs);
            } else {
              r = RAST.__default.SystemTuple(_9_exprs);
            }
            RAST._IExpr _out16;
            DCOMP._IOwnership _out17;
            (this).FromOwned(r, expectedOwnership, out _out16, out _out17);
            r = _out16;
            resultingOwnership = _out17;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _14_path = _source0.dtor_path;
          Dafny.ISequence<DAST._IType> _15_typeArgs = _source0.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _16_args = _source0.dtor_args;
          {
            RAST._IExpr _out18;
            _out18 = DCOMP.COMP.GenPathExpr(_14_path);
            r = _out18;
            if ((new BigInteger((_15_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _17_typeExprs;
              _17_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi2 = new BigInteger((_15_typeArgs).Count);
              for (BigInteger _18_i = BigInteger.Zero; _18_i < _hi2; _18_i++) {
                RAST._IType _19_typeExpr;
                RAST._IType _out19;
                _out19 = (this).GenType((_15_typeArgs).Select(_18_i), DCOMP.GenTypeContext.@default());
                _19_typeExpr = _out19;
                _17_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_17_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_19_typeExpr));
              }
              r = (r).ApplyType(_17_typeExprs);
            }
            r = (r).MSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _20_arguments;
            _20_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi3 = new BigInteger((_16_args).Count);
            for (BigInteger _21_i = BigInteger.Zero; _21_i < _hi3; _21_i++) {
              RAST._IExpr _22_recursiveGen;
              DCOMP._IOwnership _23___v160;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _24_recIdents;
              RAST._IExpr _out20;
              DCOMP._IOwnership _out21;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out22;
              (this).GenExpr((_16_args).Select(_21_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out20, out _out21, out _out22);
              _22_recursiveGen = _out20;
              _23___v160 = _out21;
              _24_recIdents = _out22;
              _20_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_20_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_22_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _24_recIdents);
            }
            r = (r).Apply(_20_arguments);
            RAST._IExpr _out23;
            DCOMP._IOwnership _out24;
            (this).FromOwned(r, expectedOwnership, out _out23, out _out24);
            r = _out23;
            resultingOwnership = _out24;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_NewUninitArray) {
          Dafny.ISequence<DAST._IExpression> _25_dims = _source0.dtor_dims;
          DAST._IType _26_typ = _source0.dtor_typ;
          {
            if ((new BigInteger(16)) < (new BigInteger((_25_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _27_msg;
              _27_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_27_msg);
              }
              r = RAST.Expr.create_RawExpr(_27_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _28_typeGen;
              RAST._IType _out25;
              _out25 = (this).GenType(_26_typ, DCOMP.GenTypeContext.@default());
              _28_typeGen = _out25;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _29_dimExprs;
              _29_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi4 = new BigInteger((_25_dims).Count);
              for (BigInteger _30_i = BigInteger.Zero; _30_i < _hi4; _30_i++) {
                RAST._IExpr _31_recursiveGen;
                DCOMP._IOwnership _32___v161;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _33_recIdents;
                RAST._IExpr _out26;
                DCOMP._IOwnership _out27;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out28;
                (this).GenExpr((_25_dims).Select(_30_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out26, out _out27, out _out28);
                _31_recursiveGen = _out26;
                _32___v161 = _out27;
                _33_recIdents = _out28;
                _29_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_29_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.IntoUsize(_31_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _33_recIdents);
              }
              if ((new BigInteger((_25_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _34_class__name;
                _34_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_25_dims).Count)));
                r = ((((RAST.__default.dafny__runtime).MSel(_34_class__name)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_28_typeGen))).MSel((this).placebos__usize)).Apply(_29_dimExprs);
              } else {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_28_typeGen))).Apply(_29_dimExprs);
              }
            }
            RAST._IExpr _out29;
            DCOMP._IOwnership _out30;
            (this).FromOwned(r, expectedOwnership, out _out29, out _out30);
            r = _out29;
            resultingOwnership = _out30;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_ArrayIndexToInt) {
          DAST._IExpression _35_underlying = _source0.dtor_value;
          {
            RAST._IExpr _36_recursiveGen;
            DCOMP._IOwnership _37___v162;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _38_recIdents;
            RAST._IExpr _out31;
            DCOMP._IOwnership _out32;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out33;
            (this).GenExpr(_35_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out31, out _out32, out _out33);
            _36_recursiveGen = _out31;
            _37___v162 = _out32;
            _38_recIdents = _out33;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(_36_recursiveGen);
            readIdents = _38_recIdents;
            RAST._IExpr _out34;
            DCOMP._IOwnership _out35;
            (this).FromOwned(r, expectedOwnership, out _out34, out _out35);
            r = _out34;
            resultingOwnership = _out35;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_FinalizeNewArray) {
          DAST._IExpression _39_underlying = _source0.dtor_value;
          DAST._IType _40_typ = _source0.dtor_typ;
          {
            RAST._IType _41_tpe;
            RAST._IType _out36;
            _out36 = (this).GenType(_40_typ, DCOMP.GenTypeContext.@default());
            _41_tpe = _out36;
            RAST._IExpr _42_recursiveGen;
            DCOMP._IOwnership _43___v163;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _44_recIdents;
            RAST._IExpr _out37;
            DCOMP._IOwnership _out38;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out39;
            (this).GenExpr(_39_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out37, out _out38, out _out39);
            _42_recursiveGen = _out37;
            _43___v163 = _out38;
            _44_recIdents = _out39;
            readIdents = _44_recIdents;
            if ((_41_tpe).IsObjectOrPointer()) {
              RAST._IType _45_t;
              _45_t = (_41_tpe).ObjectOrPointerUnderlying();
              if ((_45_t).is_Array) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).array__construct)).Apply1(_42_recursiveGen);
              } else if ((_45_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _46_c;
                _46_c = (_45_t).MultiArrayClass();
                r = (((RAST.__default.dafny__runtime).MSel(_46_c)).MSel((this).array__construct)).Apply1(_42_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_41_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_41_tpe)._ToString(DCOMP.__default.IND)));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            }
            RAST._IExpr _out40;
            DCOMP._IOwnership _out41;
            (this).FromOwned(r, expectedOwnership, out _out40, out _out41);
            r = _out40;
            resultingOwnership = _out41;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_DatatypeValue) {
          DAST._IResolvedType _47_datatypeType = _source0.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _48_typeArgs = _source0.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _49_variant = _source0.dtor_variant;
          bool _50_isCo = _source0.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _51_values = _source0.dtor_contents;
          {
            RAST._IExpr _out42;
            _out42 = DCOMP.COMP.GenPathExpr((_47_datatypeType).dtor_path);
            r = _out42;
            Dafny.ISequence<RAST._IType> _52_genTypeArgs;
            _52_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi5 = new BigInteger((_48_typeArgs).Count);
            for (BigInteger _53_i = BigInteger.Zero; _53_i < _hi5; _53_i++) {
              RAST._IType _54_typeExpr;
              RAST._IType _out43;
              _out43 = (this).GenType((_48_typeArgs).Select(_53_i), DCOMP.GenTypeContext.@default());
              _54_typeExpr = _out43;
              _52_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_52_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_54_typeExpr));
            }
            if ((new BigInteger((_48_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_52_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_49_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _55_assignments;
            _55_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi6 = new BigInteger((_51_values).Count);
            for (BigInteger _56_i = BigInteger.Zero; _56_i < _hi6; _56_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs0 = (_51_values).Select(_56_i);
              Dafny.ISequence<Dafny.Rune> _57_name = _let_tmp_rhs0.dtor__0;
              DAST._IExpression _58_value = _let_tmp_rhs0.dtor__1;
              if (_50_isCo) {
                RAST._IExpr _59_recursiveGen;
                DCOMP._IOwnership _60___v164;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _61_recIdents;
                RAST._IExpr _out44;
                DCOMP._IOwnership _out45;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out46;
                (this).GenExpr(_58_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out44, out _out45, out _out46);
                _59_recursiveGen = _out44;
                _60___v164 = _out45;
                _61_recIdents = _out46;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _61_recIdents);
                Dafny.ISequence<Dafny.Rune> _62_allReadCloned;
                _62_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_61_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _63_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_0 in (_61_recIdents).Elements) {
                    _63_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_0;
                    if ((_61_recIdents).Contains(_63_next)) {
                      goto after__ASSIGN_SUCH_THAT_0;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4402)");
                after__ASSIGN_SUCH_THAT_0: ;
                  _62_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_62_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _63_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _63_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _61_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_61_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_63_next));
                }
                Dafny.ISequence<Dafny.Rune> _64_wasAssigned;
                _64_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _62_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_59_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _55_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_55_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_57_name), RAST.Expr.create_RawExpr(_64_wasAssigned))));
              } else {
                RAST._IExpr _65_recursiveGen;
                DCOMP._IOwnership _66___v165;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _67_recIdents;
                RAST._IExpr _out47;
                DCOMP._IOwnership _out48;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out49;
                (this).GenExpr(_58_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out47, out _out48, out _out49);
                _65_recursiveGen = _out47;
                _66___v165 = _out48;
                _67_recIdents = _out49;
                _55_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_55_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_57_name), _65_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _67_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _55_assignments);
            if ((this).IsRcWrapped((_47_datatypeType).dtor_attributes)) {
              r = RAST.__default.RcNew(r);
            }
            RAST._IExpr _out50;
            DCOMP._IOwnership _out51;
            (this).FromOwned(r, expectedOwnership, out _out50, out _out51);
            r = _out50;
            resultingOwnership = _out51;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Convert) {
          {
            RAST._IExpr _out52;
            DCOMP._IOwnership _out53;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out54;
            (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out52, out _out53, out _out54);
            r = _out52;
            resultingOwnership = _out53;
            readIdents = _out54;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SeqConstruct) {
          DAST._IExpression _68_length = _source0.dtor_length;
          DAST._IExpression _69_expr = _source0.dtor_elem;
          {
            RAST._IExpr _70_recursiveGen;
            DCOMP._IOwnership _71___v169;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _72_recIdents;
            RAST._IExpr _out55;
            DCOMP._IOwnership _out56;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out57;
            (this).GenExpr(_69_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out55, out _out56, out _out57);
            _70_recursiveGen = _out55;
            _71___v169 = _out56;
            _72_recIdents = _out57;
            RAST._IExpr _73_lengthGen;
            DCOMP._IOwnership _74___v170;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _75_lengthIdents;
            RAST._IExpr _out58;
            DCOMP._IOwnership _out59;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out60;
            (this).GenExpr(_68_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out58, out _out59, out _out60);
            _73_lengthGen = _out58;
            _74___v170 = _out59;
            _75_lengthIdents = _out60;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_70_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_73_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_72_recIdents, _75_lengthIdents);
            RAST._IExpr _out61;
            DCOMP._IOwnership _out62;
            (this).FromOwned(r, expectedOwnership, out _out61, out _out62);
            r = _out61;
            resultingOwnership = _out62;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _76_exprs = _source0.dtor_elements;
          DAST._IType _77_typ = _source0.dtor_typ;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _78_genTpe;
            RAST._IType _out63;
            _out63 = (this).GenType(_77_typ, DCOMP.GenTypeContext.@default());
            _78_genTpe = _out63;
            BigInteger _79_i;
            _79_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _80_args;
            _80_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_79_i) < (new BigInteger((_76_exprs).Count))) {
              RAST._IExpr _81_recursiveGen;
              DCOMP._IOwnership _82___v171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _83_recIdents;
              RAST._IExpr _out64;
              DCOMP._IOwnership _out65;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out66;
              (this).GenExpr((_76_exprs).Select(_79_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out64, out _out65, out _out66);
              _81_recursiveGen = _out64;
              _82___v171 = _out65;
              _83_recIdents = _out66;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _83_recIdents);
              _80_args = Dafny.Sequence<RAST._IExpr>.Concat(_80_args, Dafny.Sequence<RAST._IExpr>.FromElements(_81_recursiveGen));
              _79_i = (_79_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_80_args);
            if ((new BigInteger((_80_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_78_genTpe));
            }
            RAST._IExpr _out67;
            DCOMP._IOwnership _out68;
            (this).FromOwned(r, expectedOwnership, out _out67, out _out68);
            r = _out67;
            resultingOwnership = _out68;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _84_exprs = _source0.dtor_elements;
          {
            Dafny.ISequence<RAST._IExpr> _85_generatedValues;
            _85_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _86_i;
            _86_i = BigInteger.Zero;
            while ((_86_i) < (new BigInteger((_84_exprs).Count))) {
              RAST._IExpr _87_recursiveGen;
              DCOMP._IOwnership _88___v172;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _89_recIdents;
              RAST._IExpr _out69;
              DCOMP._IOwnership _out70;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out71;
              (this).GenExpr((_84_exprs).Select(_86_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out69, out _out70, out _out71);
              _87_recursiveGen = _out69;
              _88___v172 = _out70;
              _89_recIdents = _out71;
              _85_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_85_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_87_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _89_recIdents);
              _86_i = (_86_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_85_generatedValues);
            RAST._IExpr _out72;
            DCOMP._IOwnership _out73;
            (this).FromOwned(r, expectedOwnership, out _out72, out _out73);
            r = _out72;
            resultingOwnership = _out73;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _90_exprs = _source0.dtor_elements;
          {
            Dafny.ISequence<RAST._IExpr> _91_generatedValues;
            _91_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _92_i;
            _92_i = BigInteger.Zero;
            while ((_92_i) < (new BigInteger((_90_exprs).Count))) {
              RAST._IExpr _93_recursiveGen;
              DCOMP._IOwnership _94___v173;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _95_recIdents;
              RAST._IExpr _out74;
              DCOMP._IOwnership _out75;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out76;
              (this).GenExpr((_90_exprs).Select(_92_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out74, out _out75, out _out76);
              _93_recursiveGen = _out74;
              _94___v173 = _out75;
              _95_recIdents = _out76;
              _91_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_91_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_93_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _95_recIdents);
              _92_i = (_92_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_91_generatedValues);
            RAST._IExpr _out77;
            DCOMP._IOwnership _out78;
            (this).FromOwned(r, expectedOwnership, out _out77, out _out78);
            r = _out77;
            resultingOwnership = _out78;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_ToMultiset) {
          DAST._IExpression _96_expr = _source0.dtor_ToMultiset_a0;
          {
            RAST._IExpr _97_recursiveGen;
            DCOMP._IOwnership _98___v174;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _99_recIdents;
            RAST._IExpr _out79;
            DCOMP._IOwnership _out80;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out81;
            (this).GenExpr(_96_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out79, out _out80, out _out81);
            _97_recursiveGen = _out79;
            _98___v174 = _out80;
            _99_recIdents = _out81;
            r = ((_97_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _99_recIdents;
            RAST._IExpr _out82;
            DCOMP._IOwnership _out83;
            (this).FromOwned(r, expectedOwnership, out _out82, out _out83);
            r = _out82;
            resultingOwnership = _out83;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _100_mapElems = _source0.dtor_mapElems;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _101_generatedValues;
            _101_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _102_i;
            _102_i = BigInteger.Zero;
            while ((_102_i) < (new BigInteger((_100_mapElems).Count))) {
              RAST._IExpr _103_recursiveGenKey;
              DCOMP._IOwnership _104___v175;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _105_recIdentsKey;
              RAST._IExpr _out84;
              DCOMP._IOwnership _out85;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out86;
              (this).GenExpr(((_100_mapElems).Select(_102_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out84, out _out85, out _out86);
              _103_recursiveGenKey = _out84;
              _104___v175 = _out85;
              _105_recIdentsKey = _out86;
              RAST._IExpr _106_recursiveGenValue;
              DCOMP._IOwnership _107___v176;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _108_recIdentsValue;
              RAST._IExpr _out87;
              DCOMP._IOwnership _out88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out89;
              (this).GenExpr(((_100_mapElems).Select(_102_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out87, out _out88, out _out89);
              _106_recursiveGenValue = _out87;
              _107___v176 = _out88;
              _108_recIdentsValue = _out89;
              _101_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_101_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_103_recursiveGenKey, _106_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _105_recIdentsKey), _108_recIdentsValue);
              _102_i = (_102_i) + (BigInteger.One);
            }
            _102_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _109_arguments;
            _109_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_102_i) < (new BigInteger((_101_generatedValues).Count))) {
              RAST._IExpr _110_genKey;
              _110_genKey = ((_101_generatedValues).Select(_102_i)).dtor__0;
              RAST._IExpr _111_genValue;
              _111_genValue = ((_101_generatedValues).Select(_102_i)).dtor__1;
              _109_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_109_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _110_genKey, _111_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _102_i = (_102_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_109_arguments);
            RAST._IExpr _out90;
            DCOMP._IOwnership _out91;
            (this).FromOwned(r, expectedOwnership, out _out90, out _out91);
            r = _out90;
            resultingOwnership = _out91;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SeqUpdate) {
          DAST._IExpression _112_expr = _source0.dtor_expr;
          DAST._IExpression _113_index = _source0.dtor_indexExpr;
          DAST._IExpression _114_value = _source0.dtor_value;
          {
            RAST._IExpr _115_exprR;
            DCOMP._IOwnership _116___v177;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _117_exprIdents;
            RAST._IExpr _out92;
            DCOMP._IOwnership _out93;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out94;
            (this).GenExpr(_112_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out92, out _out93, out _out94);
            _115_exprR = _out92;
            _116___v177 = _out93;
            _117_exprIdents = _out94;
            RAST._IExpr _118_indexR;
            DCOMP._IOwnership _119_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _120_indexIdents;
            RAST._IExpr _out95;
            DCOMP._IOwnership _out96;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out97;
            (this).GenExpr(_113_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out95, out _out96, out _out97);
            _118_indexR = _out95;
            _119_indexOwnership = _out96;
            _120_indexIdents = _out97;
            RAST._IExpr _121_valueR;
            DCOMP._IOwnership _122_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _123_valueIdents;
            RAST._IExpr _out98;
            DCOMP._IOwnership _out99;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out100;
            (this).GenExpr(_114_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out98, out _out99, out _out100);
            _121_valueR = _out98;
            _122_valueOwnership = _out99;
            _123_valueIdents = _out100;
            r = ((_115_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_118_indexR, _121_valueR));
            RAST._IExpr _out101;
            DCOMP._IOwnership _out102;
            (this).FromOwned(r, expectedOwnership, out _out101, out _out102);
            r = _out101;
            resultingOwnership = _out102;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_117_exprIdents, _120_indexIdents), _123_valueIdents);
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapUpdate) {
          DAST._IExpression _124_expr = _source0.dtor_expr;
          DAST._IExpression _125_index = _source0.dtor_indexExpr;
          DAST._IExpression _126_value = _source0.dtor_value;
          {
            RAST._IExpr _127_exprR;
            DCOMP._IOwnership _128___v178;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _129_exprIdents;
            RAST._IExpr _out103;
            DCOMP._IOwnership _out104;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out105;
            (this).GenExpr(_124_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out103, out _out104, out _out105);
            _127_exprR = _out103;
            _128___v178 = _out104;
            _129_exprIdents = _out105;
            RAST._IExpr _130_indexR;
            DCOMP._IOwnership _131_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _132_indexIdents;
            RAST._IExpr _out106;
            DCOMP._IOwnership _out107;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out108;
            (this).GenExpr(_125_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out106, out _out107, out _out108);
            _130_indexR = _out106;
            _131_indexOwnership = _out107;
            _132_indexIdents = _out108;
            RAST._IExpr _133_valueR;
            DCOMP._IOwnership _134_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _135_valueIdents;
            RAST._IExpr _out109;
            DCOMP._IOwnership _out110;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out111;
            (this).GenExpr(_126_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out109, out _out110, out _out111);
            _133_valueR = _out109;
            _134_valueOwnership = _out110;
            _135_valueIdents = _out111;
            r = ((_127_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_130_indexR, _133_valueR));
            RAST._IExpr _out112;
            DCOMP._IOwnership _out113;
            (this).FromOwned(r, expectedOwnership, out _out112, out _out113);
            r = _out112;
            resultingOwnership = _out113;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_129_exprIdents, _132_indexIdents), _135_valueIdents);
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_This) {
          {
            DCOMP._ISelfInfo _source1 = selfIdent;
            {
              if (_source1.is_ThisTyped) {
                Dafny.ISequence<Dafny.Rune> _136_id = _source1.dtor_rSelfName;
                DAST._IType _137_dafnyType = _source1.dtor_dafnyType;
                {
                  RAST._IExpr _out114;
                  DCOMP._IOwnership _out115;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
                  (this).GenIdent(_136_id, selfIdent, env, expectedOwnership, out _out114, out _out115, out _out116);
                  r = _out114;
                  resultingOwnership = _out115;
                  readIdents = _out116;
                }
                goto after_match1;
              }
            }
            {
              DCOMP._ISelfInfo _138_None = _source1;
              {
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")"));
                RAST._IExpr _out117;
                DCOMP._IOwnership _out118;
                (this).FromOwned(r, expectedOwnership, out _out117, out _out118);
                r = _out117;
                resultingOwnership = _out118;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              }
            }
          after_match1: ;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Ite) {
          DAST._IExpression _139_cond = _source0.dtor_cond;
          DAST._IExpression _140_t = _source0.dtor_thn;
          DAST._IExpression _141_f = _source0.dtor_els;
          {
            RAST._IExpr _142_cond;
            DCOMP._IOwnership _143___v179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _144_recIdentsCond;
            RAST._IExpr _out119;
            DCOMP._IOwnership _out120;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out121;
            (this).GenExpr(_139_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out119, out _out120, out _out121);
            _142_cond = _out119;
            _143___v179 = _out120;
            _144_recIdentsCond = _out121;
            RAST._IExpr _145_fExpr;
            DCOMP._IOwnership _146_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _147_recIdentsF;
            RAST._IExpr _out122;
            DCOMP._IOwnership _out123;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out124;
            (this).GenExpr(_141_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out122, out _out123, out _out124);
            _145_fExpr = _out122;
            _146_fOwned = _out123;
            _147_recIdentsF = _out124;
            RAST._IExpr _148_tExpr;
            DCOMP._IOwnership _149___v180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _150_recIdentsT;
            RAST._IExpr _out125;
            DCOMP._IOwnership _out126;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out127;
            (this).GenExpr(_140_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out125, out _out126, out _out127);
            _148_tExpr = _out125;
            _149___v180 = _out126;
            _150_recIdentsT = _out127;
            r = RAST.Expr.create_IfExpr(_142_cond, _148_tExpr, _145_fExpr);
            RAST._IExpr _out128;
            DCOMP._IOwnership _out129;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out128, out _out129);
            r = _out128;
            resultingOwnership = _out129;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_144_recIdentsCond, _150_recIdentsT), _147_recIdentsF);
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source0.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _151_e = _source0.dtor_expr;
            DAST.Format._IUnaryOpFormat _152_format = _source0.dtor_format1;
            {
              RAST._IExpr _153_recursiveGen;
              DCOMP._IOwnership _154___v181;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _155_recIdents;
              RAST._IExpr _out130;
              DCOMP._IOwnership _out131;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out132;
              (this).GenExpr(_151_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out130, out _out131, out _out132);
              _153_recursiveGen = _out130;
              _154___v181 = _out131;
              _155_recIdents = _out132;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _153_recursiveGen, _152_format);
              RAST._IExpr _out133;
              DCOMP._IOwnership _out134;
              (this).FromOwned(r, expectedOwnership, out _out133, out _out134);
              r = _out133;
              resultingOwnership = _out134;
              readIdents = _155_recIdents;
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source0.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _156_e = _source0.dtor_expr;
            DAST.Format._IUnaryOpFormat _157_format = _source0.dtor_format1;
            {
              RAST._IExpr _158_recursiveGen;
              DCOMP._IOwnership _159___v182;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _160_recIdents;
              RAST._IExpr _out135;
              DCOMP._IOwnership _out136;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
              (this).GenExpr(_156_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out135, out _out136, out _out137);
              _158_recursiveGen = _out135;
              _159___v182 = _out136;
              _160_recIdents = _out137;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _158_recursiveGen, _157_format);
              RAST._IExpr _out138;
              DCOMP._IOwnership _out139;
              (this).FromOwned(r, expectedOwnership, out _out138, out _out139);
              r = _out138;
              resultingOwnership = _out139;
              readIdents = _160_recIdents;
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source0.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _161_e = _source0.dtor_expr;
            DAST.Format._IUnaryOpFormat _162_format = _source0.dtor_format1;
            {
              RAST._IExpr _163_recursiveGen;
              DCOMP._IOwnership _164_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _165_recIdents;
              RAST._IExpr _out140;
              DCOMP._IOwnership _out141;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out142;
              (this).GenExpr(_161_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out140, out _out141, out _out142);
              _163_recursiveGen = _out140;
              _164_recOwned = _out141;
              _165_recIdents = _out142;
              r = ((_163_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out143;
              DCOMP._IOwnership _out144;
              (this).FromOwned(r, expectedOwnership, out _out143, out _out144);
              r = _out143;
              resultingOwnership = _out144;
              readIdents = _165_recIdents;
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_BinOp) {
          RAST._IExpr _out145;
          DCOMP._IOwnership _out146;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out147;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out145, out _out146, out _out147);
          r = _out145;
          resultingOwnership = _out146;
          readIdents = _out147;
          goto after_match0;
        }
      }
      {
        if (_source0.is_ArrayLen) {
          DAST._IExpression _166_expr = _source0.dtor_expr;
          DAST._IType _167_exprType = _source0.dtor_exprType;
          BigInteger _168_dim = _source0.dtor_dim;
          bool _169_native = _source0.dtor_native;
          {
            RAST._IExpr _170_recursiveGen;
            DCOMP._IOwnership _171___v187;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _172_recIdents;
            RAST._IExpr _out148;
            DCOMP._IOwnership _out149;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out150;
            (this).GenExpr(_166_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out148, out _out149, out _out150);
            _170_recursiveGen = _out148;
            _171___v187 = _out149;
            _172_recIdents = _out150;
            RAST._IType _173_arrayType;
            RAST._IType _out151;
            _out151 = (this).GenType(_167_exprType, DCOMP.GenTypeContext.@default());
            _173_arrayType = _out151;
            if (!((_173_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _174_msg;
              _174_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_173_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_174_msg);
              r = RAST.Expr.create_RawExpr(_174_msg);
            } else {
              RAST._IType _175_underlying;
              _175_underlying = (_173_arrayType).ObjectOrPointerUnderlying();
              if (((_168_dim).Sign == 0) && ((_175_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_170_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_168_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_170_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = ((((this).read__macro).Apply1(_170_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("length"), Std.Strings.__default.OfNat(_168_dim)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_usize")))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                }
              }
              if (!(_169_native)) {
                r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(r);
              }
            }
            RAST._IExpr _out152;
            DCOMP._IOwnership _out153;
            (this).FromOwned(r, expectedOwnership, out _out152, out _out153);
            r = _out152;
            resultingOwnership = _out153;
            readIdents = _172_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapKeys) {
          DAST._IExpression _176_expr = _source0.dtor_expr;
          {
            RAST._IExpr _177_recursiveGen;
            DCOMP._IOwnership _178___v188;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _179_recIdents;
            RAST._IExpr _out154;
            DCOMP._IOwnership _out155;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
            (this).GenExpr(_176_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out154, out _out155, out _out156);
            _177_recursiveGen = _out154;
            _178___v188 = _out155;
            _179_recIdents = _out156;
            readIdents = _179_recIdents;
            r = ((_177_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out157;
            DCOMP._IOwnership _out158;
            (this).FromOwned(r, expectedOwnership, out _out157, out _out158);
            r = _out157;
            resultingOwnership = _out158;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapValues) {
          DAST._IExpression _180_expr = _source0.dtor_expr;
          {
            RAST._IExpr _181_recursiveGen;
            DCOMP._IOwnership _182___v189;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _183_recIdents;
            RAST._IExpr _out159;
            DCOMP._IOwnership _out160;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out161;
            (this).GenExpr(_180_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out159, out _out160, out _out161);
            _181_recursiveGen = _out159;
            _182___v189 = _out160;
            _183_recIdents = _out161;
            readIdents = _183_recIdents;
            r = ((_181_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out162;
            DCOMP._IOwnership _out163;
            (this).FromOwned(r, expectedOwnership, out _out162, out _out163);
            r = _out162;
            resultingOwnership = _out163;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SelectFn) {
          DAST._IExpression _184_on = _source0.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _185_field = _source0.dtor_field;
          bool _186_isDatatype = _source0.dtor_onDatatype;
          bool _187_isStatic = _source0.dtor_isStatic;
          BigInteger _188_arity = _source0.dtor_arity;
          {
            RAST._IExpr _189_onExpr;
            DCOMP._IOwnership _190_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _191_recIdents;
            RAST._IExpr _out164;
            DCOMP._IOwnership _out165;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out166;
            (this).GenExpr(_184_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out164, out _out165, out _out166);
            _189_onExpr = _out164;
            _190_onOwned = _out165;
            _191_recIdents = _out166;
            Dafny.ISequence<Dafny.Rune> _192_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _193_onString;
            _193_onString = (_189_onExpr)._ToString(DCOMP.__default.IND);
            if (_187_isStatic) {
              _192_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_193_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_185_field));
            } else {
              _192_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _192_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_192_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _193_onString), ((object.Equals(_190_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _194_args;
              _194_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _195_i;
              _195_i = BigInteger.Zero;
              while ((_195_i) < (_188_arity)) {
                if ((_195_i).Sign == 1) {
                  _194_args = Dafny.Sequence<Dafny.Rune>.Concat(_194_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _194_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_194_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_195_i));
                _195_i = (_195_i) + (BigInteger.One);
              }
              _192_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_192_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _194_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _192_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_192_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_185_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _194_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _192_s = Dafny.Sequence<Dafny.Rune>.Concat(_192_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _192_s = Dafny.Sequence<Dafny.Rune>.Concat(_192_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _196_typeShape;
            _196_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _197_i;
            _197_i = BigInteger.Zero;
            while ((_197_i) < (_188_arity)) {
              if ((_197_i).Sign == 1) {
                _196_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_196_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _196_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_196_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _197_i = (_197_i) + (BigInteger.One);
            }
            _196_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_196_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _192_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _192_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _196_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_192_s);
            RAST._IExpr _out167;
            DCOMP._IOwnership _out168;
            (this).FromOwned(r, expectedOwnership, out _out167, out _out168);
            r = _out167;
            resultingOwnership = _out168;
            readIdents = _191_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Select) {
          DAST._IExpression expr0 = _source0.dtor_expr;
          if (expr0.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _198_c = expr0.dtor_Companion_a0;
            Dafny.ISequence<DAST._IType> _199_typeArgs = expr0.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _200_field = _source0.dtor_field;
            bool _201_isConstant = _source0.dtor_isConstant;
            bool _202_isDatatype = _source0.dtor_onDatatype;
            DAST._IType _203_fieldType = _source0.dtor_fieldType;
            {
              RAST._IExpr _204_onExpr;
              DCOMP._IOwnership _205_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _206_recIdents;
              RAST._IExpr _out169;
              DCOMP._IOwnership _out170;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out171;
              (this).GenExpr(DAST.Expression.create_Companion(_198_c, _199_typeArgs), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out169, out _out170, out _out171);
              _204_onExpr = _out169;
              _205_onOwned = _out170;
              _206_recIdents = _out171;
              r = ((_204_onExpr).MSel(DCOMP.__default.escapeName(_200_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out172;
              DCOMP._IOwnership _out173;
              (this).FromOwned(r, expectedOwnership, out _out172, out _out173);
              r = _out172;
              resultingOwnership = _out173;
              readIdents = _206_recIdents;
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_Select) {
          DAST._IExpression _207_on = _source0.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _208_field = _source0.dtor_field;
          bool _209_isConstant = _source0.dtor_isConstant;
          bool _210_isDatatype = _source0.dtor_onDatatype;
          DAST._IType _211_fieldType = _source0.dtor_fieldType;
          {
            if (_210_isDatatype) {
              RAST._IExpr _212_onExpr;
              DCOMP._IOwnership _213_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _214_recIdents;
              RAST._IExpr _out174;
              DCOMP._IOwnership _out175;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out176;
              (this).GenExpr(_207_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out174, out _out175, out _out176);
              _212_onExpr = _out174;
              _213_onOwned = _out175;
              _214_recIdents = _out176;
              r = ((_212_onExpr).Sel(DCOMP.__default.escapeName(_208_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _215_typ;
              RAST._IType _out177;
              _out177 = (this).GenType(_211_fieldType, DCOMP.GenTypeContext.@default());
              _215_typ = _out177;
              RAST._IExpr _out178;
              DCOMP._IOwnership _out179;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out178, out _out179);
              r = _out178;
              resultingOwnership = _out179;
              readIdents = _214_recIdents;
            } else {
              RAST._IExpr _216_onExpr;
              DCOMP._IOwnership _217_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _218_recIdents;
              RAST._IExpr _out180;
              DCOMP._IOwnership _out181;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out182;
              (this).GenExpr(_207_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out180, out _out181, out _out182);
              _216_onExpr = _out180;
              _217_onOwned = _out181;
              _218_recIdents = _out182;
              r = _216_onExpr;
              if (!object.Equals(_216_onExpr, RAST.__default.self)) {
                RAST._IExpr _source2 = _216_onExpr;
                {
                  if (_source2.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> op10 = _source2.dtor_op1;
                    if (object.Equals(op10, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                      RAST._IExpr underlying0 = _source2.dtor_underlying;
                      if (underlying0.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name0 = underlying0.dtor_name;
                        if (object.Equals(name0, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
                          goto after_match2;
                        }
                      }
                    }
                  }
                }
                {
                }
              after_match2: ;
                if (((this).ObjectType).is_RcMut) {
                  r = (r).Clone();
                }
                r = ((this).read__macro).Apply1(r);
              }
              r = (r).Sel(DCOMP.__default.escapeName(_208_field));
              if (_209_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out183;
              DCOMP._IOwnership _out184;
              (this).FromOwned(r, expectedOwnership, out _out183, out _out184);
              r = _out183;
              resultingOwnership = _out184;
              readIdents = _218_recIdents;
            }
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Index) {
          DAST._IExpression _219_on = _source0.dtor_expr;
          DAST._ICollKind _220_collKind = _source0.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _221_indices = _source0.dtor_indices;
          {
            RAST._IExpr _222_onExpr;
            DCOMP._IOwnership _223_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _224_recIdents;
            RAST._IExpr _out185;
            DCOMP._IOwnership _out186;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out187;
            (this).GenExpr(_219_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out185, out _out186, out _out187);
            _222_onExpr = _out185;
            _223_onOwned = _out186;
            _224_recIdents = _out187;
            readIdents = _224_recIdents;
            r = _222_onExpr;
            bool _225_hadArray;
            _225_hadArray = false;
            if (object.Equals(_220_collKind, DAST.CollKind.create_Array())) {
              r = ((this).read__macro).Apply1(r);
              _225_hadArray = true;
              if ((new BigInteger((_221_indices).Count)) > (BigInteger.One)) {
                r = (r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
              }
            }
            BigInteger _hi7 = new BigInteger((_221_indices).Count);
            for (BigInteger _226_i = BigInteger.Zero; _226_i < _hi7; _226_i++) {
              if (object.Equals(_220_collKind, DAST.CollKind.create_Array())) {
                RAST._IExpr _227_idx;
                DCOMP._IOwnership _228_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _229_recIdentsIdx;
                RAST._IExpr _out188;
                DCOMP._IOwnership _out189;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out190;
                (this).GenExpr((_221_indices).Select(_226_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out188, out _out189, out _out190);
                _227_idx = _out188;
                _228_idxOwned = _out189;
                _229_recIdentsIdx = _out190;
                _227_idx = RAST.__default.IntoUsize(_227_idx);
                r = RAST.Expr.create_SelectIndex(r, _227_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _229_recIdentsIdx);
              } else {
                RAST._IExpr _230_idx;
                DCOMP._IOwnership _231_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _232_recIdentsIdx;
                RAST._IExpr _out191;
                DCOMP._IOwnership _out192;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out193;
                (this).GenExpr((_221_indices).Select(_226_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out191, out _out192, out _out193);
                _230_idx = _out191;
                _231_idxOwned = _out192;
                _232_recIdentsIdx = _out193;
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_230_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _232_recIdentsIdx);
              }
            }
            if (_225_hadArray) {
              r = (r).Clone();
            }
            RAST._IExpr _out194;
            DCOMP._IOwnership _out195;
            (this).FromOwned(r, expectedOwnership, out _out194, out _out195);
            r = _out194;
            resultingOwnership = _out195;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_IndexRange) {
          DAST._IExpression _233_on = _source0.dtor_expr;
          bool _234_isArray = _source0.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _235_low = _source0.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _236_high = _source0.dtor_high;
          {
            RAST._IExpr _237_onExpr;
            DCOMP._IOwnership _238_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _239_recIdents;
            RAST._IExpr _out196;
            DCOMP._IOwnership _out197;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out198;
            (this).GenExpr(_233_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out196, out _out197, out _out198);
            _237_onExpr = _out196;
            _238_onOwned = _out197;
            _239_recIdents = _out198;
            readIdents = _239_recIdents;
            Dafny.ISequence<Dafny.Rune> _240_methodName;
            if ((_235_low).is_Some) {
              if ((_236_high).is_Some) {
                _240_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice");
              } else {
                _240_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop");
              }
            } else if ((_236_high).is_Some) {
              _240_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take");
            } else {
              _240_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            }
            Dafny.ISequence<RAST._IExpr> _241_arguments;
            _241_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source3 = _235_low;
            {
              if (_source3.is_Some) {
                DAST._IExpression _242_l = _source3.dtor_value;
                {
                  RAST._IExpr _243_lExpr;
                  DCOMP._IOwnership _244___v192;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _245_recIdentsL;
                  RAST._IExpr _out199;
                  DCOMP._IOwnership _out200;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out201;
                  (this).GenExpr(_242_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out199, out _out200, out _out201);
                  _243_lExpr = _out199;
                  _244___v192 = _out200;
                  _245_recIdentsL = _out201;
                  _241_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_241_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_243_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _245_recIdentsL);
                }
                goto after_match3;
              }
            }
            {
            }
          after_match3: ;
            Std.Wrappers._IOption<DAST._IExpression> _source4 = _236_high;
            {
              if (_source4.is_Some) {
                DAST._IExpression _246_h = _source4.dtor_value;
                {
                  RAST._IExpr _247_hExpr;
                  DCOMP._IOwnership _248___v193;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _249_recIdentsH;
                  RAST._IExpr _out202;
                  DCOMP._IOwnership _out203;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out204;
                  (this).GenExpr(_246_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out202, out _out203, out _out204);
                  _247_hExpr = _out202;
                  _248___v193 = _out203;
                  _249_recIdentsH = _out204;
                  _241_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_241_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_247_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _249_recIdentsH);
                }
                goto after_match4;
              }
            }
            {
            }
          after_match4: ;
            r = _237_onExpr;
            if (_234_isArray) {
              if (!(_240_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _240_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _240_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _240_methodName))).Apply(_241_arguments);
            } else {
              if (!(_240_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_240_methodName)).Apply(_241_arguments);
              }
            }
            RAST._IExpr _out205;
            DCOMP._IOwnership _out206;
            (this).FromOwned(r, expectedOwnership, out _out205, out _out206);
            r = _out205;
            resultingOwnership = _out206;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_TupleSelect) {
          DAST._IExpression _250_on = _source0.dtor_expr;
          BigInteger _251_idx = _source0.dtor_index;
          DAST._IType _252_fieldType = _source0.dtor_fieldType;
          {
            RAST._IExpr _253_onExpr;
            DCOMP._IOwnership _254_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _255_recIdents;
            RAST._IExpr _out207;
            DCOMP._IOwnership _out208;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out209;
            (this).GenExpr(_250_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out207, out _out208, out _out209);
            _253_onExpr = _out207;
            _254_onOwnership = _out208;
            _255_recIdents = _out209;
            Dafny.ISequence<Dafny.Rune> _256_selName;
            _256_selName = Std.Strings.__default.OfNat(_251_idx);
            DAST._IType _source5 = _252_fieldType;
            {
              if (_source5.is_Tuple) {
                Dafny.ISequence<DAST._IType> _257_tps = _source5.dtor_Tuple_a0;
                if (((_252_fieldType).is_Tuple) && ((new BigInteger((_257_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _256_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _256_selName);
                }
                goto after_match5;
              }
            }
            {
            }
          after_match5: ;
            r = ((_253_onExpr).Sel(_256_selName)).Clone();
            RAST._IExpr _out210;
            DCOMP._IOwnership _out211;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out210, out _out211);
            r = _out210;
            resultingOwnership = _out211;
            readIdents = _255_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Call) {
          DAST._IExpression _258_on = _source0.dtor_on;
          DAST._ICallName _259_name = _source0.dtor_callName;
          Dafny.ISequence<DAST._IType> _260_typeArgs = _source0.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _261_args = _source0.dtor_args;
          {
            Dafny.ISequence<RAST._IExpr> _262_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _263_recIdents;
            Dafny.ISequence<RAST._IType> _264_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _265_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out212;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out213;
            Dafny.ISequence<RAST._IType> _out214;
            Std.Wrappers._IOption<DAST._IResolvedType> _out215;
            (this).GenArgs(selfIdent, _259_name, _260_typeArgs, _261_args, env, out _out212, out _out213, out _out214, out _out215);
            _262_argExprs = _out212;
            _263_recIdents = _out213;
            _264_typeExprs = _out214;
            _265_fullNameQualifier = _out215;
            readIdents = _263_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source6 = _265_fullNameQualifier;
            {
              if (_source6.is_Some) {
                DAST._IResolvedType value0 = _source6.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _266_path = value0.dtor_path;
                Dafny.ISequence<DAST._IType> _267_onTypeArgs = value0.dtor_typeArgs;
                DAST._IResolvedTypeBase _268_base = value0.dtor_kind;
                RAST._IExpr _269_fullPath;
                RAST._IExpr _out216;
                _out216 = DCOMP.COMP.GenPathExpr(_266_path);
                _269_fullPath = _out216;
                Dafny.ISequence<RAST._IType> _270_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out217;
                _out217 = (this).GenTypeArgs(_267_onTypeArgs, DCOMP.GenTypeContext.@default());
                _270_onTypeExprs = _out217;
                RAST._IExpr _271_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _272_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _273_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_268_base).is_Trait) || ((_268_base).is_Class)) {
                  RAST._IExpr _out218;
                  DCOMP._IOwnership _out219;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out220;
                  (this).GenExpr(_258_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out218, out _out219, out _out220);
                  _271_onExpr = _out218;
                  _272_recOwnership = _out219;
                  _273_recIdents = _out220;
                  _271_onExpr = ((this).read__macro).Apply1(_271_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _273_recIdents);
                } else {
                  RAST._IExpr _out221;
                  DCOMP._IOwnership _out222;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out223;
                  (this).GenExpr(_258_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out221, out _out222, out _out223);
                  _271_onExpr = _out221;
                  _272_recOwnership = _out222;
                  _273_recIdents = _out223;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _273_recIdents);
                }
                r = ((((_269_fullPath).ApplyType(_270_onTypeExprs)).MSel(DCOMP.__default.escapeName((_259_name).dtor_name))).ApplyType(_264_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_271_onExpr), _262_argExprs));
                RAST._IExpr _out224;
                DCOMP._IOwnership _out225;
                (this).FromOwned(r, expectedOwnership, out _out224, out _out225);
                r = _out224;
                resultingOwnership = _out225;
                goto after_match6;
              }
            }
            {
              RAST._IExpr _274_onExpr;
              DCOMP._IOwnership _275___v199;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _276_recIdents;
              RAST._IExpr _out226;
              DCOMP._IOwnership _out227;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out228;
              (this).GenExpr(_258_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out226, out _out227, out _out228);
              _274_onExpr = _out226;
              _275___v199 = _out227;
              _276_recIdents = _out228;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _276_recIdents);
              Dafny.ISequence<Dafny.Rune> _277_renderedName;
              DAST._ICallName _source7 = _259_name;
              {
                if (_source7.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _278_ident = _source7.dtor_name;
                  _277_renderedName = DCOMP.__default.escapeName(_278_ident);
                  goto after_match7;
                }
              }
              {
                bool disjunctiveMatch0 = false;
                if (_source7.is_MapBuilderAdd) {
                  disjunctiveMatch0 = true;
                }
                if (_source7.is_SetBuilderAdd) {
                  disjunctiveMatch0 = true;
                }
                if (disjunctiveMatch0) {
                  _277_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                  goto after_match7;
                }
              }
              {
                _277_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
              }
            after_match7: ;
              DAST._IExpression _source8 = _258_on;
              {
                if (_source8.is_Companion) {
                  {
                    _274_onExpr = (_274_onExpr).MSel(_277_renderedName);
                  }
                  goto after_match8;
                }
              }
              {
                {
                  if (!object.Equals(_274_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source9 = _259_name;
                    {
                      if (_source9.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source9.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _279_tpe = onType0.dtor_value;
                          RAST._IType _280_typ;
                          RAST._IType _out229;
                          _out229 = (this).GenType(_279_tpe, DCOMP.GenTypeContext.@default());
                          _280_typ = _out229;
                          if ((_280_typ).IsObjectOrPointer()) {
                            _274_onExpr = ((this).read__macro).Apply1(_274_onExpr);
                          }
                          goto after_match9;
                        }
                      }
                    }
                    {
                    }
                  after_match9: ;
                  }
                  _274_onExpr = (_274_onExpr).Sel(_277_renderedName);
                }
              }
            after_match8: ;
              r = ((_274_onExpr).ApplyType(_264_typeExprs)).Apply(_262_argExprs);
              RAST._IExpr _out230;
              DCOMP._IOwnership _out231;
              (this).FromOwned(r, expectedOwnership, out _out230, out _out231);
              r = _out230;
              resultingOwnership = _out231;
              return ;
            }
          after_match6: ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _281_paramsDafny = _source0.dtor_params;
          DAST._IType _282_retType = _source0.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _283_body = _source0.dtor_body;
          {
            Dafny.ISequence<RAST._IFormal> _284_params;
            Dafny.ISequence<RAST._IFormal> _out232;
            _out232 = (this).GenParams(_281_paramsDafny);
            _284_params = _out232;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _285_paramNames;
            _285_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _286_paramTypesMap;
            _286_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi8 = new BigInteger((_284_params).Count);
            for (BigInteger _287_i = BigInteger.Zero; _287_i < _hi8; _287_i++) {
              Dafny.ISequence<Dafny.Rune> _288_name;
              _288_name = ((_284_params).Select(_287_i)).dtor_name;
              _285_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_285_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_288_name));
              _286_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_286_paramTypesMap, _288_name, ((_284_params).Select(_287_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _289_subEnv;
            _289_subEnv = ((env).ToOwned()).merge(DCOMP.Environment.create(_285_paramNames, _286_paramTypesMap));
            RAST._IExpr _290_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _291_recIdents;
            DCOMP._IEnvironment _292___v210;
            RAST._IExpr _out233;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out234;
            DCOMP._IEnvironment _out235;
            (this).GenStmts(_283_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _289_subEnv, true, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out233, out _out234, out _out235);
            _290_recursiveGen = _out233;
            _291_recIdents = _out234;
            _292___v210 = _out235;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _291_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_291_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_293_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll0 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_0 in (_293_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _294_name = (Dafny.ISequence<Dafny.Rune>)_compr_0;
                if ((_293_paramNames).Contains(_294_name)) {
                  _coll0.Add(_294_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll0);
            }))())(_285_paramNames));
            RAST._IExpr _295_allReadCloned;
            _295_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_291_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _296_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_1 in (_291_recIdents).Elements) {
                _296_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_1;
                if ((_291_recIdents).Contains(_296_next)) {
                  goto after__ASSIGN_SUCH_THAT_1;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 4877)");
            after__ASSIGN_SUCH_THAT_1: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_296_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _297_selfCloned;
                DCOMP._IOwnership _298___v211;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _299___v212;
                RAST._IExpr _out236;
                DCOMP._IOwnership _out237;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out238;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out236, out _out237, out _out238);
                _297_selfCloned = _out236;
                _298___v211 = _out237;
                _299___v212 = _out238;
                _295_allReadCloned = (_295_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_297_selfCloned)));
              } else if (!((_285_paramNames).Contains(_296_next))) {
                RAST._IExpr _300_copy;
                _300_copy = (RAST.Expr.create_Identifier(_296_next)).Clone();
                _295_allReadCloned = (_295_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _296_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_300_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_296_next));
              }
              _291_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_291_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_296_next));
            }
            RAST._IType _301_retTypeGen;
            RAST._IType _out239;
            _out239 = (this).GenType(_282_retType, DCOMP.GenTypeContext.InFn());
            _301_retTypeGen = _out239;
            r = RAST.Expr.create_Block((_295_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_284_params, Std.Wrappers.Option<RAST._IType>.create_Some(_301_retTypeGen), RAST.Expr.create_Block(_290_recursiveGen)))));
            RAST._IExpr _out240;
            DCOMP._IOwnership _out241;
            (this).FromOwned(r, expectedOwnership, out _out240, out _out241);
            r = _out240;
            resultingOwnership = _out241;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _302_values = _source0.dtor_values;
          DAST._IType _303_retType = _source0.dtor_retType;
          DAST._IExpression _304_expr = _source0.dtor_expr;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _305_paramNames;
            _305_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _306_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out242;
            _out242 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_307_value) => {
              return (_307_value).dtor__0;
            })), _302_values));
            _306_paramFormals = _out242;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _308_paramTypes;
            _308_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _309_paramNamesSet;
            _309_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi9 = new BigInteger((_302_values).Count);
            for (BigInteger _310_i = BigInteger.Zero; _310_i < _hi9; _310_i++) {
              Dafny.ISequence<Dafny.Rune> _311_name;
              _311_name = (((_302_values).Select(_310_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _312_rName;
              _312_rName = DCOMP.__default.escapeName(_311_name);
              _305_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_305_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_312_rName));
              _308_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_308_paramTypes, _312_rName, ((_306_paramFormals).Select(_310_i)).dtor_tpe);
              _309_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_309_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_312_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi10 = new BigInteger((_302_values).Count);
            for (BigInteger _313_i = BigInteger.Zero; _313_i < _hi10; _313_i++) {
              RAST._IType _314_typeGen;
              RAST._IType _out243;
              _out243 = (this).GenType((((_302_values).Select(_313_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.InFn());
              _314_typeGen = _out243;
              RAST._IExpr _315_valueGen;
              DCOMP._IOwnership _316___v213;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _317_recIdents;
              RAST._IExpr _out244;
              DCOMP._IOwnership _out245;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out246;
              (this).GenExpr(((_302_values).Select(_313_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out244, out _out245, out _out246);
              _315_valueGen = _out244;
              _316___v213 = _out245;
              _317_recIdents = _out246;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_302_values).Select(_313_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_314_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_315_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _317_recIdents);
            }
            DCOMP._IEnvironment _318_newEnv;
            _318_newEnv = DCOMP.Environment.create(_305_paramNames, _308_paramTypes);
            RAST._IExpr _319_recGen;
            DCOMP._IOwnership _320_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _321_recIdents;
            RAST._IExpr _out247;
            DCOMP._IOwnership _out248;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out249;
            (this).GenExpr(_304_expr, selfIdent, _318_newEnv, expectedOwnership, out _out247, out _out248, out _out249);
            _319_recGen = _out247;
            _320_recOwned = _out248;
            _321_recIdents = _out249;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_321_recIdents, _309_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_319_recGen));
            RAST._IExpr _out250;
            DCOMP._IOwnership _out251;
            (this).FromOwnership(r, _320_recOwned, expectedOwnership, out _out250, out _out251);
            r = _out250;
            resultingOwnership = _out251;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _322_name = _source0.dtor_ident;
          DAST._IType _323_tpe = _source0.dtor_typ;
          DAST._IExpression _324_value = _source0.dtor_value;
          DAST._IExpression _325_iifeBody = _source0.dtor_iifeBody;
          {
            RAST._IExpr _326_valueGen;
            DCOMP._IOwnership _327___v214;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _328_recIdents;
            RAST._IExpr _out252;
            DCOMP._IOwnership _out253;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out254;
            (this).GenExpr(_324_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out252, out _out253, out _out254);
            _326_valueGen = _out252;
            _327___v214 = _out253;
            _328_recIdents = _out254;
            readIdents = _328_recIdents;
            RAST._IType _329_valueTypeGen;
            RAST._IType _out255;
            _out255 = (this).GenType(_323_tpe, DCOMP.GenTypeContext.InFn());
            _329_valueTypeGen = _out255;
            RAST._IExpr _330_bodyGen;
            DCOMP._IOwnership _331___v215;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _332_bodyIdents;
            RAST._IExpr _out256;
            DCOMP._IOwnership _out257;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out258;
            (this).GenExpr(_325_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out256, out _out257, out _out258);
            _330_bodyGen = _out256;
            _331___v215 = _out257;
            _332_bodyIdents = _out258;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_332_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_322_name)))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_322_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_329_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_326_valueGen))).Then(_330_bodyGen));
            RAST._IExpr _out259;
            DCOMP._IOwnership _out260;
            (this).FromOwned(r, expectedOwnership, out _out259, out _out260);
            r = _out259;
            resultingOwnership = _out260;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Apply) {
          DAST._IExpression _333_func = _source0.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _334_args = _source0.dtor_args;
          {
            RAST._IExpr _335_funcExpr;
            DCOMP._IOwnership _336___v216;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _337_recIdents;
            RAST._IExpr _out261;
            DCOMP._IOwnership _out262;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out263;
            (this).GenExpr(_333_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out261, out _out262, out _out263);
            _335_funcExpr = _out261;
            _336___v216 = _out262;
            _337_recIdents = _out263;
            readIdents = _337_recIdents;
            Dafny.ISequence<RAST._IExpr> _338_rArgs;
            _338_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi11 = new BigInteger((_334_args).Count);
            for (BigInteger _339_i = BigInteger.Zero; _339_i < _hi11; _339_i++) {
              RAST._IExpr _340_argExpr;
              DCOMP._IOwnership _341_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _342_argIdents;
              RAST._IExpr _out264;
              DCOMP._IOwnership _out265;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out266;
              (this).GenExpr((_334_args).Select(_339_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out264, out _out265, out _out266);
              _340_argExpr = _out264;
              _341_argOwned = _out265;
              _342_argIdents = _out266;
              _338_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_338_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_340_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _342_argIdents);
            }
            r = (_335_funcExpr).Apply(_338_rArgs);
            RAST._IExpr _out267;
            DCOMP._IOwnership _out268;
            (this).FromOwned(r, expectedOwnership, out _out267, out _out268);
            r = _out267;
            resultingOwnership = _out268;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_TypeTest) {
          DAST._IExpression _343_on = _source0.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _344_dType = _source0.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _345_variant = _source0.dtor_variant;
          {
            RAST._IExpr _346_exprGen;
            DCOMP._IOwnership _347___v217;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _348_recIdents;
            RAST._IExpr _out269;
            DCOMP._IOwnership _out270;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out271;
            (this).GenExpr(_343_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out269, out _out270, out _out271);
            _346_exprGen = _out269;
            _347___v217 = _out270;
            _348_recIdents = _out271;
            RAST._IType _349_dTypePath;
            RAST._IType _out272;
            _out272 = DCOMP.COMP.GenPath(_344_dType);
            _349_dTypePath = _out272;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_346_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_349_dTypePath).MSel(DCOMP.__default.escapeName(_345_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out273;
            DCOMP._IOwnership _out274;
            (this).FromOwned(r, expectedOwnership, out _out273, out _out274);
            r = _out273;
            resultingOwnership = _out274;
            readIdents = _348_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_BoolBoundedPool) {
          {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
            RAST._IExpr _out275;
            DCOMP._IOwnership _out276;
            (this).FromOwned(r, expectedOwnership, out _out275, out _out276);
            r = _out275;
            resultingOwnership = _out276;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SetBoundedPool) {
          DAST._IExpression _350_of = _source0.dtor_of;
          {
            RAST._IExpr _351_exprGen;
            DCOMP._IOwnership _352___v218;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _353_recIdents;
            RAST._IExpr _out277;
            DCOMP._IOwnership _out278;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out279;
            (this).GenExpr(_350_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out277, out _out278, out _out279);
            _351_exprGen = _out277;
            _352___v218 = _out278;
            _353_recIdents = _out279;
            r = ((_351_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out280;
            DCOMP._IOwnership _out281;
            (this).FromOwned(r, expectedOwnership, out _out280, out _out281);
            r = _out280;
            resultingOwnership = _out281;
            readIdents = _353_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SeqBoundedPool) {
          DAST._IExpression _354_of = _source0.dtor_of;
          bool _355_includeDuplicates = _source0.dtor_includeDuplicates;
          {
            RAST._IExpr _356_exprGen;
            DCOMP._IOwnership _357___v219;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _358_recIdents;
            RAST._IExpr _out282;
            DCOMP._IOwnership _out283;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out284;
            (this).GenExpr(_354_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out282, out _out283, out _out284);
            _356_exprGen = _out282;
            _357___v219 = _out283;
            _358_recIdents = _out284;
            r = ((_356_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_355_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out285;
            DCOMP._IOwnership _out286;
            (this).FromOwned(r, expectedOwnership, out _out285, out _out286);
            r = _out285;
            resultingOwnership = _out286;
            readIdents = _358_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapBoundedPool) {
          DAST._IExpression _359_of = _source0.dtor_of;
          {
            RAST._IExpr _360_exprGen;
            DCOMP._IOwnership _361___v220;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _362_recIdents;
            RAST._IExpr _out287;
            DCOMP._IOwnership _out288;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out289;
            (this).GenExpr(_359_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out287, out _out288, out _out289);
            _360_exprGen = _out287;
            _361___v220 = _out288;
            _362_recIdents = _out289;
            r = ((((_360_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _362_recIdents;
            RAST._IExpr _out290;
            DCOMP._IOwnership _out291;
            (this).FromOwned(r, expectedOwnership, out _out290, out _out291);
            r = _out290;
            resultingOwnership = _out291;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_IntRange) {
          DAST._IExpression _363_lo = _source0.dtor_lo;
          DAST._IExpression _364_hi = _source0.dtor_hi;
          bool _365_up = _source0.dtor_up;
          {
            RAST._IExpr _366_lo;
            DCOMP._IOwnership _367___v221;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _368_recIdentsLo;
            RAST._IExpr _out292;
            DCOMP._IOwnership _out293;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out294;
            (this).GenExpr(_363_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out292, out _out293, out _out294);
            _366_lo = _out292;
            _367___v221 = _out293;
            _368_recIdentsLo = _out294;
            RAST._IExpr _369_hi;
            DCOMP._IOwnership _370___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _371_recIdentsHi;
            RAST._IExpr _out295;
            DCOMP._IOwnership _out296;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out297;
            (this).GenExpr(_364_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out295, out _out296, out _out297);
            _369_hi = _out295;
            _370___v222 = _out296;
            _371_recIdentsHi = _out297;
            if (_365_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_366_lo, _369_hi));
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_369_hi, _366_lo));
            }
            RAST._IExpr _out298;
            DCOMP._IOwnership _out299;
            (this).FromOwned(r, expectedOwnership, out _out298, out _out299);
            r = _out298;
            resultingOwnership = _out299;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_368_recIdentsLo, _371_recIdentsHi);
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_UnboundedIntRange) {
          DAST._IExpression _372_start = _source0.dtor_start;
          bool _373_up = _source0.dtor_up;
          {
            RAST._IExpr _374_start;
            DCOMP._IOwnership _375___v223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _376_recIdentStart;
            RAST._IExpr _out300;
            DCOMP._IOwnership _out301;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out302;
            (this).GenExpr(_372_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out300, out _out301, out _out302);
            _374_start = _out300;
            _375___v223 = _out301;
            _376_recIdentStart = _out302;
            if (_373_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).Apply1(_374_start);
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).Apply1(_374_start);
            }
            RAST._IExpr _out303;
            DCOMP._IOwnership _out304;
            (this).FromOwned(r, expectedOwnership, out _out303, out _out304);
            r = _out303;
            resultingOwnership = _out304;
            readIdents = _376_recIdentStart;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapBuilder) {
          DAST._IType _377_keyType = _source0.dtor_keyType;
          DAST._IType _378_valueType = _source0.dtor_valueType;
          {
            RAST._IType _379_kType;
            RAST._IType _out305;
            _out305 = (this).GenType(_377_keyType, DCOMP.GenTypeContext.@default());
            _379_kType = _out305;
            RAST._IType _380_vType;
            RAST._IType _out306;
            _out306 = (this).GenType(_378_valueType, DCOMP.GenTypeContext.@default());
            _380_vType = _out306;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_379_kType, _380_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out307;
            DCOMP._IOwnership _out308;
            (this).FromOwned(r, expectedOwnership, out _out307, out _out308);
            r = _out307;
            resultingOwnership = _out308;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SetBuilder) {
          DAST._IType _381_elemType = _source0.dtor_elemType;
          {
            RAST._IType _382_eType;
            RAST._IType _out309;
            _out309 = (this).GenType(_381_elemType, DCOMP.GenTypeContext.@default());
            _382_eType = _out309;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_382_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out310;
            DCOMP._IOwnership _out311;
            (this).FromOwned(r, expectedOwnership, out _out310, out _out311);
            r = _out310;
            resultingOwnership = _out311;
            return ;
          }
          goto after_match0;
        }
      }
      {
        DAST._IType _383_elemType = _source0.dtor_elemType;
        DAST._IExpression _384_collection = _source0.dtor_collection;
        bool _385_is__forall = _source0.dtor_is__forall;
        DAST._IExpression _386_lambda = _source0.dtor_lambda;
        {
          RAST._IType _387_tpe;
          RAST._IType _out312;
          _out312 = (this).GenType(_383_elemType, DCOMP.GenTypeContext.@default());
          _387_tpe = _out312;
          RAST._IExpr _388_collectionGen;
          DCOMP._IOwnership _389___v224;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _390_recIdents;
          RAST._IExpr _out313;
          DCOMP._IOwnership _out314;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out315;
          (this).GenExpr(_384_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out313, out _out314, out _out315);
          _388_collectionGen = _out313;
          _389___v224 = _out314;
          _390_recIdents = _out315;
          Dafny.ISequence<DAST._IAttribute> _391_extraAttributes;
          _391_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_384_collection).is_IntRange) || ((_384_collection).is_UnboundedIntRange)) || ((_384_collection).is_SeqBoundedPool)) {
            _391_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_386_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _392_formals;
            _392_formals = (_386_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _393_newFormals;
            _393_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi12 = new BigInteger((_392_formals).Count);
            for (BigInteger _394_i = BigInteger.Zero; _394_i < _hi12; _394_i++) {
              var _pat_let_tv0 = _391_extraAttributes;
              var _pat_let_tv1 = _392_formals;
              _393_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_393_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_392_formals).Select(_394_i), _pat_let34_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let34_0, _395_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv0, ((_pat_let_tv1).Select(_394_i)).dtor_attributes), _pat_let35_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let35_0, _396_dt__update_hattributes_h0 => DAST.Formal.create((_395_dt__update__tmp_h0).dtor_name, (_395_dt__update__tmp_h0).dtor_typ, _396_dt__update_hattributes_h0)))))));
            }
            DAST._IExpression _397_newLambda;
            DAST._IExpression _398_dt__update__tmp_h1 = _386_lambda;
            Dafny.ISequence<DAST._IFormal> _399_dt__update_hparams_h0 = _393_newFormals;
            _397_newLambda = DAST.Expression.create_Lambda(_399_dt__update_hparams_h0, (_398_dt__update__tmp_h1).dtor_retType, (_398_dt__update__tmp_h1).dtor_body);
            RAST._IExpr _400_lambdaGen;
            DCOMP._IOwnership _401___v225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _402_recLambdaIdents;
            RAST._IExpr _out316;
            DCOMP._IOwnership _out317;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out318;
            (this).GenExpr(_397_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out316, out _out317, out _out318);
            _400_lambdaGen = _out316;
            _401___v225 = _out317;
            _402_recLambdaIdents = _out318;
            Dafny.ISequence<Dafny.Rune> _403_fn;
            if (_385_is__forall) {
              _403_fn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all");
            } else {
              _403_fn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any");
            }
            r = ((_388_collectionGen).Sel(_403_fn)).Apply1(((_400_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_390_recIdents, _402_recLambdaIdents);
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Quantifier without an inline lambda"));
            r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
          RAST._IExpr _out319;
          DCOMP._IOwnership _out320;
          (this).FromOwned(r, expectedOwnership, out _out319, out _out320);
          r = _out319;
          resultingOwnership = _out320;
        }
      }
    after_match0: ;
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      BigInteger _0_i;
      _0_i = BigInteger.Zero;
      while ((_0_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _1_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _2_m;
        RAST._IMod _out0;
        _out0 = (this).GenModule((p).Select(_0_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2_m = _out0;
        _1_generated = (_2_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_0_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _1_generated);
        _0_i = (_0_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _0_i;
      _0_i = BigInteger.Zero;
      while ((_0_i) < (new BigInteger((fullName).Count))) {
        if ((_0_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_0_i)));
        _0_i = (_0_i) + (BigInteger.One);
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