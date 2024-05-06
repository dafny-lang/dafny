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
      Dafny.ISequence<Dafny.Rune> _1057___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1057___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1057___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1057___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in123 = (i).Drop(new BigInteger(2));
        i = _in123;
        goto TAIL_CALL_START;
      } else {
        _1057___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1057___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in124 = (i).Drop(BigInteger.One);
        i = _in124;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1058___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1058___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1058___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1058___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in125 = (i).Drop(BigInteger.One);
        i = _in125;
        goto TAIL_CALL_START;
      } else {
        _1058___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1058___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
      } else if ((DCOMP.__default.reserved__rust).Contains(i)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), i);
      } else if (DCOMP.__default.is__idiomatic__rust__id(i)) {
        return DCOMP.__default.idiomatic__rust(i);
      } else if (DCOMP.__default.is__dafny__generated__id(i)) {
        return i;
      } else {
        Dafny.ISequence<Dafny.Rune> _1059_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1059_r);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> AddAssignedPrefix(Dafny.ISequence<Dafny.Rune> rustName) {
      if (((new BigInteger((rustName).Count)) >= (new BigInteger(2))) && (((rustName).Subsequence(BigInteger.Zero, new BigInteger(2))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.ASSIGNED__PREFIX, (rustName).Drop(new BigInteger(2)));
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.ASSIGNED__PREFIX, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_")), rustName);
      }
    }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__rust { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("async"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("await"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("const"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("continue"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("crate"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("else"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("enum"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("for"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("loop"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mod"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mut"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ref"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Self"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("static"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("struct"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("trait"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("union"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsafe"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("use"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("where"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Keywords"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("The"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abstract"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("become"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("box"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("do"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("final"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("macro"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("override"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("priv"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("try"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("typeof"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsized"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("virtual"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("yield"));
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
    public DCOMP._IEnvironment RemoveAssigned(Dafny.ISequence<Dafny.Rune> name) {
      BigInteger _1060_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1060_indexInEnv), ((this).dtor_names).Drop((_1060_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
      Dafny.ISequence<Dafny.Rune> _1061_modName;
      _1061_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_1061_modName);
      } else {
        Dafny.ISequence<RAST._IModDecl> _1062_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _1062_body = _out15;
        s = RAST.Mod.create_Mod(_1061_modName, _1062_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi5 = new BigInteger((body).Count);
      for (BigInteger _1063_i = BigInteger.Zero; _1063_i < _hi5; _1063_i++) {
        Dafny.ISequence<RAST._IModDecl> _1064_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source47 = (body).Select(_1063_i);
        bool unmatched47 = true;
        if (unmatched47) {
          if (_source47.is_Module) {
            DAST._IModule _1065_m = _source47.dtor_Module_a0;
            unmatched47 = false;
            RAST._IMod _1066_mm;
            RAST._IMod _out16;
            _out16 = (this).GenModule(_1065_m, containingPath);
            _1066_mm = _out16;
            _1064_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1066_mm));
          }
        }
        if (unmatched47) {
          if (_source47.is_Class) {
            DAST._IClass _1067_c = _source47.dtor_Class_a0;
            unmatched47 = false;
            Dafny.ISequence<RAST._IModDecl> _out17;
            _out17 = (this).GenClass(_1067_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1067_c).dtor_name)));
            _1064_generated = _out17;
          }
        }
        if (unmatched47) {
          if (_source47.is_Trait) {
            DAST._ITrait _1068_t = _source47.dtor_Trait_a0;
            unmatched47 = false;
            Dafny.ISequence<Dafny.Rune> _1069_tt;
            Dafny.ISequence<Dafny.Rune> _out18;
            _out18 = (this).GenTrait(_1068_t, containingPath);
            _1069_tt = _out18;
            _1064_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_RawDecl(_1069_tt));
          }
        }
        if (unmatched47) {
          if (_source47.is_Newtype) {
            DAST._INewtype _1070_n = _source47.dtor_Newtype_a0;
            unmatched47 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenNewtype(_1070_n);
            _1064_generated = _out19;
          }
        }
        if (unmatched47) {
          if (_source47.is_SynonymType) {
            DAST._ISynonymType _1071_s = _source47.dtor_SynonymType_a0;
            unmatched47 = false;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenSynonymType(_1071_s);
            _1064_generated = _out20;
          }
        }
        if (unmatched47) {
          DAST._IDatatype _1072_d = _source47.dtor_Datatype_a0;
          unmatched47 = false;
          Dafny.ISequence<RAST._IModDecl> _out21;
          _out21 = (this).GenDatatype(_1072_d);
          _1064_generated = _out21;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1064_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1073_genTpConstraint;
      _1073_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1073_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1073_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1073_genTpConstraint);
    }
    public void GenTypeParameters(Dafny.ISequence<DAST._ITypeArgDecl> @params, out Dafny.ISet<DAST._IType> typeParamsSet, out Dafny.ISequence<RAST._IType> typeParams, out Dafny.ISequence<RAST._ITypeParamDecl> constrainedTypeParams, out Dafny.ISequence<Dafny.Rune> whereConstraints)
    {
      typeParamsSet = Dafny.Set<DAST._IType>.Empty;
      typeParams = Dafny.Sequence<RAST._IType>.Empty;
      constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Empty;
      whereConstraints = Dafny.Sequence<Dafny.Rune>.Empty;
      typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      whereConstraints = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      if ((new BigInteger((@params).Count)).Sign == 1) {
        BigInteger _hi6 = new BigInteger((@params).Count);
        for (BigInteger _1074_tpI = BigInteger.Zero; _1074_tpI < _hi6; _1074_tpI++) {
          DAST._ITypeArgDecl _1075_tp;
          _1075_tp = (@params).Select(_1074_tpI);
          DAST._IType _1076_typeArg;
          RAST._ITypeParamDecl _1077_typeParam;
          DAST._IType _out22;
          RAST._ITypeParamDecl _out23;
          (this).GenTypeParam(_1075_tp, out _out22, out _out23);
          _1076_typeArg = _out22;
          _1077_typeParam = _out23;
          RAST._IType _1078_rType;
          RAST._IType _out24;
          _out24 = (this).GenType(_1076_typeArg, false, false);
          _1078_rType = _out24;
          typeParamsSet = Dafny.Set<DAST._IType>.Union(typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1076_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1078_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1077_typeParam));
        }
      }
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1079_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1080_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1081_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1082_whereConstraints;
      Dafny.ISet<DAST._IType> _out25;
      Dafny.ISequence<RAST._IType> _out26;
      Dafny.ISequence<RAST._ITypeParamDecl> _out27;
      Dafny.ISequence<Dafny.Rune> _out28;
      (this).GenTypeParameters((c).dtor_typeParams, out _out25, out _out26, out _out27, out _out28);
      _1079_typeParamsSet = _out25;
      _1080_rTypeParams = _out26;
      _1081_rTypeParamsDecls = _out27;
      _1082_whereConstraints = _out28;
      Dafny.ISequence<Dafny.Rune> _1083_constrainedTypeParams;
      _1083_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1081_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1084_fields;
      _1084_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1085_fieldInits;
      _1085_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1086_fieldI = BigInteger.Zero; _1086_fieldI < _hi7; _1086_fieldI++) {
        DAST._IField _1087_field;
        _1087_field = ((c).dtor_fields).Select(_1086_fieldI);
        RAST._IType _1088_fieldType;
        RAST._IType _out29;
        _out29 = (this).GenType(((_1087_field).dtor_formal).dtor_typ, false, false);
        _1088_fieldType = _out29;
        Dafny.ISequence<Dafny.Rune> _1089_fieldRustName;
        _1089_fieldRustName = DCOMP.__default.escapeName(((_1087_field).dtor_formal).dtor_name);
        _1084_fields = Dafny.Sequence<RAST._IField>.Concat(_1084_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1089_fieldRustName, _1088_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source48 = (_1087_field).dtor_defaultValue;
        bool unmatched48 = true;
        if (unmatched48) {
          if (_source48.is_Some) {
            DAST._IExpression _1090_e = _source48.dtor_value;
            unmatched48 = false;
            {
              RAST._IExpr _1091_expr;
              DCOMP._IOwnership _1092___v44;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1093___v45;
              RAST._IExpr _out30;
              DCOMP._IOwnership _out31;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
              (this).GenExpr(_1090_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
              _1091_expr = _out30;
              _1092___v44 = _out31;
              _1093___v45 = _out32;
              _1085_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1085_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1089_fieldRustName, _1091_expr)));
            }
          }
        }
        if (unmatched48) {
          unmatched48 = false;
          {
            RAST._IExpr _1094_default;
            _1094_default = RAST.__default.std__Default__default;
            if ((_1088_fieldType).IsObjectOrPointer()) {
              _1094_default = (_1088_fieldType).ToNullExpr();
            }
            _1085_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1085_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1089_fieldRustName, _1094_default)));
          }
        }
      }
      BigInteger _hi8 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1095_typeParamI = BigInteger.Zero; _1095_typeParamI < _hi8; _1095_typeParamI++) {
        DAST._IType _1096_typeArg;
        RAST._ITypeParamDecl _1097_typeParam;
        DAST._IType _out33;
        RAST._ITypeParamDecl _out34;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1095_typeParamI), out _out33, out _out34);
        _1096_typeArg = _out33;
        _1097_typeParam = _out34;
        RAST._IType _1098_rTypeArg;
        RAST._IType _out35;
        _out35 = (this).GenType(_1096_typeArg, false, false);
        _1098_rTypeArg = _out35;
        _1084_fields = Dafny.Sequence<RAST._IField>.Concat(_1084_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1095_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1098_rTypeArg))))));
        _1085_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1085_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1095_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      Dafny.ISequence<Dafny.Rune> _1099_datatypeName;
      _1099_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IStruct _1100_struct;
      _1100_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1099_datatypeName, _1081_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1084_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1100_struct));
      DAST._IType _1101_underlyingDatatype;
      _1101_underlyingDatatype = DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(path, (c).dtor_attributes)));
      Dafny.ISequence<RAST._IImplMember> _1102_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1103_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out36;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out37;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_AllocatedDatatype(DAST.DatatypeType.create(path, (c).dtor_attributes))), _1079_typeParamsSet, out _out36, out _out37);
      _1102_implBodyRaw = _out36;
      _1103_traitBodies = _out37;
      Dafny.ISequence<RAST._IImplMember> _1104_implBody;
      _1104_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.Type.create_SelfOwned())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel((this).allocate)).ApplyType1(RAST.Type.create_SelfOwned())).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))))), _1102_implBodyRaw);
      RAST._IImpl _1105_i;
      _1105_i = RAST.Impl.create_Impl(_1081_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1099_datatypeName), _1080_rTypeParams), _1082_whereConstraints, _1104_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1105_i)));
      if ((new BigInteger(((c).dtor_superClasses).Count)).Sign == 1) {
        BigInteger _1106_i;
        _1106_i = BigInteger.Zero;
        while ((_1106_i) < (new BigInteger(((c).dtor_superClasses).Count))) {
          DAST._IType _1107_superClass;
          _1107_superClass = ((c).dtor_superClasses).Select(_1106_i);
          DAST._IType _source49 = _1107_superClass;
          bool unmatched49 = true;
          if (unmatched49) {
            if (_source49.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1108_traitPath = _source49.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _1109_typeArgs = _source49.dtor_typeArgs;
              DAST._IResolvedType resolved0 = _source49.dtor_resolved;
              if (resolved0.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1110___v46 = resolved0.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1111___v47 = resolved0.dtor_attributes;
                unmatched49 = false;
                {
                  RAST._IType _1112_pathStr;
                  RAST._IType _out38;
                  _out38 = DCOMP.COMP.GenPath(_1108_traitPath);
                  _1112_pathStr = _out38;
                  Dafny.ISequence<RAST._IType> _1113_typeArgs;
                  Dafny.ISequence<RAST._IType> _out39;
                  _out39 = (this).GenTypeArgs(_1109_typeArgs, false, false);
                  _1113_typeArgs = _out39;
                  Dafny.ISequence<RAST._IImplMember> _1114_body;
                  _1114_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((_1103_traitBodies).Contains(_1108_traitPath)) {
                    _1114_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1103_traitBodies,_1108_traitPath);
                  }
                  RAST._IType _1115_genSelfPath;
                  RAST._IType _out40;
                  _out40 = DCOMP.COMP.GenPath(path);
                  _1115_genSelfPath = _out40;
                  RAST._IModDecl _1116_x;
                  _1116_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1081_rTypeParamsDecls, RAST.Type.create_TypeApp(_1112_pathStr, _1113_typeArgs), RAST.Type.create_TypeApp(_1115_genSelfPath, _1080_rTypeParams), _1082_whereConstraints, _1114_body));
                  s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1116_x));
                }
              }
            }
          }
          if (unmatched49) {
            DAST._IType _1117___v48 = _source49;
            unmatched49 = false;
          }
          _1106_i = (_1106_i) + (BigInteger.One);
        }
      }
      return s;
    }
    public Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _1118_typeParamsSet;
      _1118_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1119_typeParamDecls;
      _1119_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1120_typeParams;
      _1120_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1121_tpI;
      _1121_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        while ((_1121_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._ITypeArgDecl _1122_tp;
          _1122_tp = ((t).dtor_typeParams).Select(_1121_tpI);
          DAST._IType _1123_typeArg;
          RAST._ITypeParamDecl _1124_typeParamDecl;
          DAST._IType _out41;
          RAST._ITypeParamDecl _out42;
          (this).GenTypeParam(_1122_tp, out _out41, out _out42);
          _1123_typeArg = _out41;
          _1124_typeParamDecl = _out42;
          _1118_typeParamsSet = Dafny.Set<DAST._IType>.Union(_1118_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1123_typeArg));
          _1119_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1119_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1124_typeParamDecl));
          RAST._IType _1125_typeParam;
          RAST._IType _out43;
          _out43 = (this).GenType(_1123_typeArg, false, false);
          _1125_typeParam = _out43;
          _1120_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1120_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1125_typeParam));
          _1121_tpI = (_1121_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1126_fullPath;
      _1126_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1127_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1128___v49;
      Dafny.ISequence<RAST._IImplMember> _out44;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out45;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_1126_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_1126_fullPath, (t).dtor_attributes)), _1118_typeParamsSet, out _out44, out _out45);
      _1127_implBody = _out44;
      _1128___v49 = _out45;
      s = (RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1119_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1120_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1127_implBody)))._ToString(DCOMP.__default.IND);
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1129_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1130_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1131_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1132_whereConstraints;
      Dafny.ISet<DAST._IType> _out46;
      Dafny.ISequence<RAST._IType> _out47;
      Dafny.ISequence<RAST._ITypeParamDecl> _out48;
      Dafny.ISequence<Dafny.Rune> _out49;
      (this).GenTypeParameters((c).dtor_typeParams, out _out46, out _out47, out _out48, out _out49);
      _1129_typeParamsSet = _out46;
      _1130_rTypeParams = _out47;
      _1131_rTypeParamsDecls = _out48;
      _1132_whereConstraints = _out49;
      Dafny.ISequence<Dafny.Rune> _1133_constrainedTypeParams;
      _1133_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1131_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1134_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source50 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      bool unmatched50 = true;
      if (unmatched50) {
        if (_source50.is_Some) {
          RAST._IType _1135_v = _source50.dtor_value;
          unmatched50 = false;
          _1134_underlyingType = _1135_v;
        }
      }
      if (unmatched50) {
        unmatched50 = false;
        RAST._IType _out50;
        _out50 = (this).GenType((c).dtor_base, false, false);
        _1134_underlyingType = _out50;
      }
      DAST._IType _1136_resultingType;
      _1136_resultingType = DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Newtype((c).dtor_base, (c).dtor_range, false, (c).dtor_attributes));
      Dafny.ISequence<Dafny.Rune> _1137_datatypeName;
      _1137_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1137_datatypeName, _1131_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1134_underlyingType))))));
      RAST._IExpr _1138_fnBody;
      _1138_fnBody = RAST.Expr.create_Identifier(_1137_datatypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source51 = (c).dtor_witnessExpr;
      bool unmatched51 = true;
      if (unmatched51) {
        if (_source51.is_Some) {
          DAST._IExpression _1139_e = _source51.dtor_value;
          unmatched51 = false;
          {
            DAST._IExpression _1140_e;
            _1140_e = ((object.Equals((c).dtor_base, _1136_resultingType)) ? (_1139_e) : (DAST.Expression.create_Convert(_1139_e, (c).dtor_base, _1136_resultingType)));
            RAST._IExpr _1141_eStr;
            DCOMP._IOwnership _1142___v50;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1143___v51;
            RAST._IExpr _out51;
            DCOMP._IOwnership _out52;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out53;
            (this).GenExpr(_1140_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out51, out _out52, out _out53);
            _1141_eStr = _out51;
            _1142___v50 = _out52;
            _1143___v51 = _out53;
            _1138_fnBody = (_1138_fnBody).Apply1(_1141_eStr);
          }
        }
      }
      if (unmatched51) {
        unmatched51 = false;
        {
          _1138_fnBody = (_1138_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1144_body;
      _1144_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1138_fnBody)));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1131_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1137_datatypeName), _1130_rTypeParams), _1132_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1144_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1131_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1137_datatypeName), _1130_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1131_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1137_datatypeName), _1130_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1134_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1145_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1146_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1147_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1148_whereConstraints;
      Dafny.ISet<DAST._IType> _out54;
      Dafny.ISequence<RAST._IType> _out55;
      Dafny.ISequence<RAST._ITypeParamDecl> _out56;
      Dafny.ISequence<Dafny.Rune> _out57;
      (this).GenTypeParameters((c).dtor_typeParams, out _out54, out _out55, out _out56, out _out57);
      _1145_typeParamsSet = _out54;
      _1146_rTypeParams = _out55;
      _1147_rTypeParamsDecls = _out56;
      _1148_whereConstraints = _out57;
      Dafny.ISequence<Dafny.Rune> _1149_constrainedTypeParams;
      _1149_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1147_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<Dafny.Rune> _1150_synonymTypeName;
      _1150_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _1151_resultingType;
      RAST._IType _out58;
      _out58 = (this).GenType((c).dtor_base, false, false);
      _1151_resultingType = _out58;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1150_synonymTypeName, _1147_rTypeParamsDecls, _1151_resultingType)));
      Std.Wrappers._IOption<DAST._IExpression> _source52 = (c).dtor_witnessExpr;
      bool unmatched52 = true;
      if (unmatched52) {
        if (_source52.is_Some) {
          DAST._IExpression _1152_e = _source52.dtor_value;
          unmatched52 = false;
          {
            RAST._IExpr _1153_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1154___v52;
            DCOMP._IEnvironment _1155_newEnv;
            RAST._IExpr _out59;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out60;
            DCOMP._IEnvironment _out61;
            (this).GenStmts((c).dtor_witnessStmts, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), false, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out59, out _out60, out _out61);
            _1153_rStmts = _out59;
            _1154___v52 = _out60;
            _1155_newEnv = _out61;
            RAST._IExpr _1156_rExpr;
            DCOMP._IOwnership _1157___v53;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1158___v54;
            RAST._IExpr _out62;
            DCOMP._IOwnership _out63;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out64;
            (this).GenExpr(_1152_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), _1155_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out62, out _out63, out _out64);
            _1156_rExpr = _out62;
            _1157___v53 = _out63;
            _1158___v54 = _out64;
            Dafny.ISequence<Dafny.Rune> _1159_constantName;
            _1159_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_1159_constantName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1151_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_1153_rStmts).Then(_1156_rExpr)))))));
          }
        }
      }
      if (unmatched52) {
        unmatched52 = false;
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1160_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1161_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1162_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1163_whereConstraints;
      Dafny.ISet<DAST._IType> _out65;
      Dafny.ISequence<RAST._IType> _out66;
      Dafny.ISequence<RAST._ITypeParamDecl> _out67;
      Dafny.ISequence<Dafny.Rune> _out68;
      (this).GenTypeParameters((c).dtor_typeParams, out _out65, out _out66, out _out67, out _out68);
      _1160_typeParamsSet = _out65;
      _1161_rTypeParams = _out66;
      _1162_rTypeParamsDecls = _out67;
      _1163_whereConstraints = _out68;
      Dafny.ISequence<Dafny.Rune> _1164_datatypeName;
      _1164_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1165_ctors;
      _1165_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      BigInteger _hi9 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1166_i = BigInteger.Zero; _1166_i < _hi9; _1166_i++) {
        DAST._IDatatypeCtor _1167_ctor;
        _1167_ctor = ((c).dtor_ctors).Select(_1166_i);
        Dafny.ISequence<RAST._IField> _1168_ctorArgs;
        _1168_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1169_isNumeric;
        _1169_isNumeric = false;
        BigInteger _hi10 = new BigInteger(((_1167_ctor).dtor_args).Count);
        for (BigInteger _1170_j = BigInteger.Zero; _1170_j < _hi10; _1170_j++) {
          DAST._IDatatypeDtor _1171_dtor;
          _1171_dtor = ((_1167_ctor).dtor_args).Select(_1170_j);
          RAST._IType _1172_formalType;
          RAST._IType _out69;
          _out69 = (this).GenType(((_1171_dtor).dtor_formal).dtor_typ, false, false);
          _1172_formalType = _out69;
          Dafny.ISequence<Dafny.Rune> _1173_formalName;
          _1173_formalName = DCOMP.__default.escapeName(((_1171_dtor).dtor_formal).dtor_name);
          if (((_1170_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1173_formalName))) {
            _1169_isNumeric = true;
          }
          if ((((_1170_j).Sign != 0) && (_1169_isNumeric)) && (!(Std.Strings.__default.OfNat(_1170_j)).Equals(_1173_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1173_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1170_j)));
            _1169_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1168_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1168_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1173_formalName, RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1172_formalType))))));
          } else {
            _1168_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1168_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1173_formalName, _1172_formalType))));
          }
        }
        RAST._IFields _1174_namedFields;
        _1174_namedFields = RAST.Fields.create_NamedFields(_1168_ctorArgs);
        if (_1169_isNumeric) {
          _1174_namedFields = (_1174_namedFields).ToNamelessFields();
        }
        _1165_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1165_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1167_ctor).dtor_name), _1174_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1175_selfPath;
      _1175_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1176_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1177_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out70;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out71;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(_1175_selfPath, (c).dtor_attributes))), _1160_typeParamsSet, out _out70, out _out71);
      _1176_implBodyRaw = _out70;
      _1177_traitBodies = _out71;
      Dafny.ISequence<RAST._IImplMember> _1178_implBody;
      _1178_implBody = _1176_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1179_emittedFields;
      _1179_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi11 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1180_i = BigInteger.Zero; _1180_i < _hi11; _1180_i++) {
        DAST._IDatatypeCtor _1181_ctor;
        _1181_ctor = ((c).dtor_ctors).Select(_1180_i);
        BigInteger _hi12 = new BigInteger(((_1181_ctor).dtor_args).Count);
        for (BigInteger _1182_j = BigInteger.Zero; _1182_j < _hi12; _1182_j++) {
          DAST._IDatatypeDtor _1183_dtor;
          _1183_dtor = ((_1181_ctor).dtor_args).Select(_1182_j);
          Dafny.ISequence<Dafny.Rune> _1184_callName;
          _1184_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1183_dtor).dtor_callName, DCOMP.__default.escapeName(((_1183_dtor).dtor_formal).dtor_name));
          if (!((_1179_emittedFields).Contains(_1184_callName))) {
            _1179_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1179_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1184_callName));
            RAST._IType _1185_formalType;
            RAST._IType _out72;
            _out72 = (this).GenType(((_1183_dtor).dtor_formal).dtor_typ, false, false);
            _1185_formalType = _out72;
            Dafny.ISequence<RAST._IMatchCase> _1186_cases;
            _1186_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1187_k = BigInteger.Zero; _1187_k < _hi13; _1187_k++) {
              DAST._IDatatypeCtor _1188_ctor2;
              _1188_ctor2 = ((c).dtor_ctors).Select(_1187_k);
              Dafny.ISequence<Dafny.Rune> _1189_pattern;
              _1189_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1164_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1188_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1190_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1191_hasMatchingField;
              _1191_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1192_patternInner;
              _1192_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1193_isNumeric;
              _1193_isNumeric = false;
              BigInteger _hi14 = new BigInteger(((_1188_ctor2).dtor_args).Count);
              for (BigInteger _1194_l = BigInteger.Zero; _1194_l < _hi14; _1194_l++) {
                DAST._IDatatypeDtor _1195_dtor2;
                _1195_dtor2 = ((_1188_ctor2).dtor_args).Select(_1194_l);
                Dafny.ISequence<Dafny.Rune> _1196_patternName;
                _1196_patternName = DCOMP.__default.escapeName(((_1195_dtor2).dtor_formal).dtor_name);
                if (((_1194_l).Sign == 0) && ((_1196_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1193_isNumeric = true;
                }
                if (_1193_isNumeric) {
                  _1196_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1195_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1194_l)));
                }
                if (object.Equals(((_1183_dtor).dtor_formal).dtor_name, ((_1195_dtor2).dtor_formal).dtor_name)) {
                  _1191_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1196_patternName);
                }
                _1192_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1192_patternInner, _1196_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1193_isNumeric) {
                _1189_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1189_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1192_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1189_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1189_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1192_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1191_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1190_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1191_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1190_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1191_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1190_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _1197_ctorMatch;
              _1197_ctorMatch = RAST.MatchCase.create(_1189_pattern, RAST.Expr.create_RawExpr(_1190_rhs));
              _1186_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1186_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1197_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1186_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1186_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1164_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _1198_methodBody;
            _1198_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1186_cases);
            _1178_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1178_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1184_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1185_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1198_methodBody)))));
          }
        }
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1199_types;
        _1199_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi15 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1200_typeI = BigInteger.Zero; _1200_typeI < _hi15; _1200_typeI++) {
          DAST._IType _1201_typeArg;
          RAST._ITypeParamDecl _1202_rTypeParamDecl;
          DAST._IType _out73;
          RAST._ITypeParamDecl _out74;
          (this).GenTypeParam(((c).dtor_typeParams).Select(_1200_typeI), out _out73, out _out74);
          _1201_typeArg = _out73;
          _1202_rTypeParamDecl = _out74;
          RAST._IType _1203_rTypeArg;
          RAST._IType _out75;
          _out75 = (this).GenType(_1201_typeArg, false, false);
          _1203_rTypeArg = _out75;
          _1199_types = Dafny.Sequence<RAST._IType>.Concat(_1199_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1203_rTypeArg))));
        }
        _1165_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1165_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1204_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1204_tpe);
})), _1199_types)))));
      }
      Dafny.ISequence<RAST._IModDecl> _1205_enumBody;
      _1205_enumBody = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]")), _1164_datatypeName, _1162_rTypeParamsDecls, _1165_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1162_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1164_datatypeName), _1161_rTypeParams), _1163_whereConstraints, _1178_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1206_printImplBodyCases;
      _1206_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1207_hashImplBodyCases;
      _1207_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1208_i = BigInteger.Zero; _1208_i < _hi16; _1208_i++) {
        DAST._IDatatypeCtor _1209_ctor;
        _1209_ctor = ((c).dtor_ctors).Select(_1208_i);
        Dafny.ISequence<Dafny.Rune> _1210_ctorMatch;
        _1210_ctorMatch = DCOMP.__default.escapeName((_1209_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1211_modulePrefix;
        _1211_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1212_ctorName;
        _1212_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1211_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1209_ctor).dtor_name));
        if (((new BigInteger((_1212_ctorName).Count)) >= (new BigInteger(13))) && (((_1212_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1212_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1213_printRhs;
        _1213_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1212_ctorName), (((_1209_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1214_hashRhs;
        _1214_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        bool _1215_isNumeric;
        _1215_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1216_ctorMatchInner;
        _1216_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi17 = new BigInteger(((_1209_ctor).dtor_args).Count);
        for (BigInteger _1217_j = BigInteger.Zero; _1217_j < _hi17; _1217_j++) {
          DAST._IDatatypeDtor _1218_dtor;
          _1218_dtor = ((_1209_ctor).dtor_args).Select(_1217_j);
          Dafny.ISequence<Dafny.Rune> _1219_patternName;
          _1219_patternName = DCOMP.__default.escapeName(((_1218_dtor).dtor_formal).dtor_name);
          if (((_1217_j).Sign == 0) && ((_1219_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1215_isNumeric = true;
          }
          if (_1215_isNumeric) {
            _1219_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1218_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1217_j)));
          }
          _1214_hashRhs = (_1214_hashRhs).Then(((RAST.Expr.create_Identifier(_1219_patternName)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))));
          _1216_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1216_ctorMatchInner, _1219_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1217_j).Sign == 1) {
            _1213_printRhs = (_1213_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1213_printRhs = (_1213_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1219_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))));
        }
        if (_1215_isNumeric) {
          _1210_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1210_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1216_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1210_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1210_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1216_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1209_ctor).dtor_hasAnyArgs) {
          _1213_printRhs = (_1213_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1213_printRhs = (_1213_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1206_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1206_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1164_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1210_ctorMatch), RAST.Expr.create_Block(_1213_printRhs))));
        _1207_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1207_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1164_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1210_ctorMatch), RAST.Expr.create_Block(_1214_hashRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _1206_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1206_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1164_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
        _1207_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1207_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1164_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1220_defaultConstrainedTypeParams;
      _1220_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1162_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1221_rTypeParamsDeclsWithEq;
      _1221_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1162_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1222_rTypeParamsDeclsWithHash;
      _1222_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1162_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1223_printImplBody;
      _1223_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1206_printImplBodyCases);
      RAST._IExpr _1224_hashImplBody;
      _1224_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1207_hashImplBodyCases);
      Dafny.ISequence<RAST._IModDecl> _1225_printImpl;
      _1225_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1162_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1164_datatypeName), _1161_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1162_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1164_datatypeName), _1161_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1223_printImplBody)))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1221_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1164_datatypeName), _1161_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements())), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1222_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1164_datatypeName), _1161_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1224_hashImplBody)))))));
      Dafny.ISequence<RAST._IModDecl> _1226_defaultImpl;
      _1226_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      Dafny.ISequence<RAST._IModDecl> _1227_asRefImpl;
      _1227_asRefImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1228_structName;
        _1228_structName = (RAST.Expr.create_Identifier(_1164_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1229_structAssignments;
        _1229_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi18 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1230_i = BigInteger.Zero; _1230_i < _hi18; _1230_i++) {
          DAST._IDatatypeDtor _1231_dtor;
          _1231_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1230_i);
          _1229_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1229_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1231_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1232_defaultConstrainedTypeParams;
        _1232_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1162_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1233_fullType;
        _1233_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1164_datatypeName), _1161_rTypeParams);
        _1226_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1232_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1233_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1233_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1228_structName, _1229_structAssignments))))))));
        _1227_asRefImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1162_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_1233_fullType), RAST.Type.create_Borrowed(_1233_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self)))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(_1205_enumBody, _1225_printImpl), _1226_defaultImpl), _1227_asRefImpl);
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
        BigInteger _hi19 = new BigInteger((p).Count);
        for (BigInteger _1234_i = BigInteger.Zero; _1234_i < _hi19; _1234_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1234_i))));
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
        BigInteger _hi20 = new BigInteger((p).Count);
        for (BigInteger _1235_i = BigInteger.Zero; _1235_i < _hi20; _1235_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1235_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding, bool inFn)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger((args).Count)).Sign == 1) {
        BigInteger _1236_i;
        _1236_i = BigInteger.Zero;
        while ((_1236_i) < (new BigInteger((args).Count))) {
          RAST._IType _1237_genTp;
          RAST._IType _out76;
          _out76 = (this).GenType((args).Select(_1236_i), inBinding, inFn);
          _1237_genTp = _out76;
          s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1237_genTp));
          _1236_i = (_1236_i) + (BigInteger.One);
        }
      }
      return s;
    }
    public bool IsRcWrapped(Dafny.ISequence<DAST._IAttribute> attributes) {
      return ((!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("auto-nongrowing-size"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()))) && (!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false")))))) || ((attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true")))));
    }
    public RAST._IType GenType(DAST._IType c, bool inBinding, bool inFn)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source53 = c;
      bool unmatched53 = true;
      if (unmatched53) {
        if (_source53.is_Path) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1238_p = _source53.dtor_Path_a0;
          Dafny.ISequence<DAST._IType> _1239_args = _source53.dtor_typeArgs;
          DAST._IResolvedType _1240_resolved = _source53.dtor_resolved;
          unmatched53 = false;
          {
            RAST._IType _1241_t;
            RAST._IType _out77;
            _out77 = DCOMP.COMP.GenPath(_1238_p);
            _1241_t = _out77;
            Dafny.ISequence<RAST._IType> _1242_typeArgs;
            Dafny.ISequence<RAST._IType> _out78;
            _out78 = (this).GenTypeArgs(_1239_args, inBinding, inFn);
            _1242_typeArgs = _out78;
            s = RAST.Type.create_TypeApp(_1241_t, _1242_typeArgs);
            DAST._IResolvedType _source54 = _1240_resolved;
            bool unmatched54 = true;
            if (unmatched54) {
              if (_source54.is_AllocatedDatatype) {
                DAST._IDatatypeType datatypeType0 = _source54.dtor_datatypeType;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1243___v55 = datatypeType0.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1244_attributes = datatypeType0.dtor_attributes;
                unmatched54 = false;
                {
                  s = (this).Object(s);
                }
              }
            }
            if (unmatched54) {
              if (_source54.is_Datatype) {
                DAST._IDatatypeType datatypeType1 = _source54.dtor_datatypeType;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1245___v56 = datatypeType1.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1246_attributes = datatypeType1.dtor_attributes;
                unmatched54 = false;
                {
                  if ((this).IsRcWrapped(_1246_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                  if ((this).IsRcWrapped(_1246_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched54) {
              if (_source54.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1247___v57 = _source54.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1248___v58 = _source54.dtor_attributes;
                unmatched54 = false;
                {
                  if ((_1238_p).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
                  }
                  s = (this).Object(RAST.Type.create_DynType(s));
                }
              }
            }
            if (unmatched54) {
              DAST._IType _1249_t = _source54.dtor_baseType;
              DAST._INewtypeRange _1250_range = _source54.dtor_range;
              bool _1251_erased = _source54.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1252_attributes = _source54.dtor_attributes;
              unmatched54 = false;
              {
                if (_1251_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source55 = DCOMP.COMP.NewtypeToRustType(_1249_t, _1250_range);
                  bool unmatched55 = true;
                  if (unmatched55) {
                    if (_source55.is_Some) {
                      RAST._IType _1253_v = _source55.dtor_value;
                      unmatched55 = false;
                      s = _1253_v;
                    }
                  }
                  if (unmatched55) {
                    unmatched55 = false;
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched53) {
        if (_source53.is_Nullable) {
          DAST._IType _1254_inner = _source53.dtor_Nullable_a0;
          unmatched53 = false;
          {
            RAST._IType _1255_innerExpr;
            RAST._IType _out79;
            _out79 = (this).GenType(_1254_inner, inBinding, inFn);
            _1255_innerExpr = _out79;
            s = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::option::Option")), Dafny.Sequence<RAST._IType>.FromElements(_1255_innerExpr));
          }
        }
      }
      if (unmatched53) {
        if (_source53.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1256_types = _source53.dtor_Tuple_a0;
          unmatched53 = false;
          {
            Dafny.ISequence<RAST._IType> _1257_args;
            _1257_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1258_i;
            _1258_i = BigInteger.Zero;
            while ((_1258_i) < (new BigInteger((_1256_types).Count))) {
              RAST._IType _1259_generated;
              RAST._IType _out80;
              _out80 = (this).GenType((_1256_types).Select(_1258_i), inBinding, inFn);
              _1259_generated = _out80;
              _1257_args = Dafny.Sequence<RAST._IType>.Concat(_1257_args, Dafny.Sequence<RAST._IType>.FromElements(_1259_generated));
              _1258_i = (_1258_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1256_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1257_args)) : (RAST.__default.SystemTupleType(_1257_args)));
          }
        }
      }
      if (unmatched53) {
        if (_source53.is_Array) {
          DAST._IType _1260_element = _source53.dtor_element;
          BigInteger _1261_dims = _source53.dtor_dims;
          unmatched53 = false;
          {
            if ((_1261_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1262_elem;
              RAST._IType _out81;
              _out81 = (this).GenType(_1260_element, inBinding, inFn);
              _1262_elem = _out81;
              if ((_1261_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1262_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1263_n;
                _1263_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1261_dims));
                s = ((RAST.__default.dafny__runtime__type).MSel(_1263_n)).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1262_elem));
                s = (this).Object(s);
              }
            }
          }
        }
      }
      if (unmatched53) {
        if (_source53.is_Seq) {
          DAST._IType _1264_element = _source53.dtor_element;
          unmatched53 = false;
          {
            RAST._IType _1265_elem;
            RAST._IType _out82;
            _out82 = (this).GenType(_1264_element, inBinding, inFn);
            _1265_elem = _out82;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1265_elem));
          }
        }
      }
      if (unmatched53) {
        if (_source53.is_Set) {
          DAST._IType _1266_element = _source53.dtor_element;
          unmatched53 = false;
          {
            RAST._IType _1267_elem;
            RAST._IType _out83;
            _out83 = (this).GenType(_1266_element, inBinding, inFn);
            _1267_elem = _out83;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1267_elem));
          }
        }
      }
      if (unmatched53) {
        if (_source53.is_Multiset) {
          DAST._IType _1268_element = _source53.dtor_element;
          unmatched53 = false;
          {
            RAST._IType _1269_elem;
            RAST._IType _out84;
            _out84 = (this).GenType(_1268_element, inBinding, inFn);
            _1269_elem = _out84;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1269_elem));
          }
        }
      }
      if (unmatched53) {
        if (_source53.is_Map) {
          DAST._IType _1270_key = _source53.dtor_key;
          DAST._IType _1271_value = _source53.dtor_value;
          unmatched53 = false;
          {
            RAST._IType _1272_keyType;
            RAST._IType _out85;
            _out85 = (this).GenType(_1270_key, inBinding, inFn);
            _1272_keyType = _out85;
            RAST._IType _1273_valueType;
            RAST._IType _out86;
            _out86 = (this).GenType(_1271_value, inBinding, inFn);
            _1273_valueType = _out86;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1272_keyType, _1273_valueType));
          }
        }
      }
      if (unmatched53) {
        if (_source53.is_MapBuilder) {
          DAST._IType _1274_key = _source53.dtor_key;
          DAST._IType _1275_value = _source53.dtor_value;
          unmatched53 = false;
          {
            RAST._IType _1276_keyType;
            RAST._IType _out87;
            _out87 = (this).GenType(_1274_key, inBinding, inFn);
            _1276_keyType = _out87;
            RAST._IType _1277_valueType;
            RAST._IType _out88;
            _out88 = (this).GenType(_1275_value, inBinding, inFn);
            _1277_valueType = _out88;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1276_keyType, _1277_valueType));
          }
        }
      }
      if (unmatched53) {
        if (_source53.is_SetBuilder) {
          DAST._IType _1278_elem = _source53.dtor_element;
          unmatched53 = false;
          {
            RAST._IType _1279_elemType;
            RAST._IType _out89;
            _out89 = (this).GenType(_1278_elem, inBinding, inFn);
            _1279_elemType = _out89;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1279_elemType));
          }
        }
      }
      if (unmatched53) {
        if (_source53.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1280_args = _source53.dtor_args;
          DAST._IType _1281_result = _source53.dtor_result;
          unmatched53 = false;
          {
            Dafny.ISequence<RAST._IType> _1282_argTypes;
            _1282_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1283_i;
            _1283_i = BigInteger.Zero;
            while ((_1283_i) < (new BigInteger((_1280_args).Count))) {
              RAST._IType _1284_generated;
              RAST._IType _out90;
              _out90 = (this).GenType((_1280_args).Select(_1283_i), inBinding, true);
              _1284_generated = _out90;
              _1282_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1282_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1284_generated)));
              _1283_i = (_1283_i) + (BigInteger.One);
            }
            RAST._IType _1285_resultType;
            RAST._IType _out91;
            _out91 = (this).GenType(_1281_result, inBinding, (inFn) || (inBinding));
            _1285_resultType = _out91;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1282_argTypes, _1285_resultType)));
          }
        }
      }
      if (unmatched53) {
        if (_source53.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h110 = _source53.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1286_name = _h110;
          unmatched53 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1286_name));
        }
      }
      if (unmatched53) {
        if (_source53.is_Primitive) {
          DAST._IPrimitive _1287_p = _source53.dtor_Primitive_a0;
          unmatched53 = false;
          {
            DAST._IPrimitive _source56 = _1287_p;
            bool unmatched56 = true;
            if (unmatched56) {
              if (_source56.is_Int) {
                unmatched56 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
              }
            }
            if (unmatched56) {
              if (_source56.is_Real) {
                unmatched56 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
              }
            }
            if (unmatched56) {
              if (_source56.is_String) {
                unmatched56 = false;
                s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
              }
            }
            if (unmatched56) {
              if (_source56.is_Bool) {
                unmatched56 = false;
                s = RAST.Type.create_Bool();
              }
            }
            if (unmatched56) {
              unmatched56 = false;
              s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
            }
          }
        }
      }
      if (unmatched53) {
        Dafny.ISequence<Dafny.Rune> _1288_v = _source53.dtor_Passthrough_a0;
        unmatched53 = false;
        s = RAST.__default.RawType(_1288_v);
      }
      return s;
    }
    public void GenClassImplBody(Dafny.ISequence<DAST._IMethod> body, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams, out Dafny.ISequence<RAST._IImplMember> s, out Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> traitBodies)
    {
      s = Dafny.Sequence<RAST._IImplMember>.Empty;
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Empty;
      s = Dafny.Sequence<RAST._IImplMember>.FromElements();
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements();
      BigInteger _hi21 = new BigInteger((body).Count);
      for (BigInteger _1289_i = BigInteger.Zero; _1289_i < _hi21; _1289_i++) {
        DAST._IMethod _source57 = (body).Select(_1289_i);
        bool unmatched57 = true;
        if (unmatched57) {
          DAST._IMethod _1290_m = _source57;
          unmatched57 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source58 = (_1290_m).dtor_overridingPath;
            bool unmatched58 = true;
            if (unmatched58) {
              if (_source58.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1291_p = _source58.dtor_value;
                unmatched58 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1292_existing;
                  _1292_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1291_p)) {
                    _1292_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1291_p);
                  }
                  RAST._IImplMember _1293_genMethod;
                  RAST._IImplMember _out92;
                  _out92 = (this).GenMethod(_1290_m, true, enclosingType, enclosingTypeParams);
                  _1293_genMethod = _out92;
                  _1292_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1292_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1293_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1291_p, _1292_existing)));
                }
              }
            }
            if (unmatched58) {
              unmatched58 = false;
              {
                RAST._IImplMember _1294_generated;
                RAST._IImplMember _out93;
                _out93 = (this).GenMethod(_1290_m, forTrait, enclosingType, enclosingTypeParams);
                _1294_generated = _out93;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1294_generated));
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
      BigInteger _hi22 = new BigInteger((@params).Count);
      for (BigInteger _1295_i = BigInteger.Zero; _1295_i < _hi22; _1295_i++) {
        DAST._IFormal _1296_param;
        _1296_param = (@params).Select(_1295_i);
        RAST._IType _1297_paramType;
        RAST._IType _out94;
        _out94 = (this).GenType((_1296_param).dtor_typ, false, false);
        _1297_paramType = _out94;
        if ((!((_1297_paramType).CanReadWithoutClone())) && (!((_1296_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1297_paramType = RAST.Type.create_Borrowed(_1297_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_1296_param).dtor_name), _1297_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1298_params;
      Dafny.ISequence<RAST._IFormal> _out95;
      _out95 = (this).GenParams((m).dtor_params);
      _1298_params = _out95;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1299_paramNames;
      _1299_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1300_paramTypes;
      _1300_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi23 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1301_paramI = BigInteger.Zero; _1301_paramI < _hi23; _1301_paramI++) {
        DAST._IFormal _1302_dafny__formal;
        _1302_dafny__formal = ((m).dtor_params).Select(_1301_paramI);
        RAST._IFormal _1303_formal;
        _1303_formal = (_1298_params).Select(_1301_paramI);
        Dafny.ISequence<Dafny.Rune> _1304_name;
        _1304_name = (_1303_formal).dtor_name;
        _1299_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1299_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1304_name));
        _1300_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1300_paramTypes, _1304_name, (_1303_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1305_fnName;
      _1305_fnName = DCOMP.__default.escapeName((m).dtor_name);
      Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1306_selfIdentifier;
      _1306_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1307_selfId;
        _1307_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((_1305_fnName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_ctor"))) {
          _1307_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        if (forTrait) {
          RAST._IFormal _1308_selfFormal;
          _1308_selfFormal = (((m).dtor_wasFunction) ? (RAST.Formal.selfBorrowed) : (RAST.Formal.selfBorrowedMut));
          _1298_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1308_selfFormal), _1298_params);
        } else {
          RAST._IType _1309_tpe;
          RAST._IType _out96;
          _out96 = (this).GenType(enclosingType, false, false);
          _1309_tpe = _out96;
          if (((_1307_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) && ((_1309_tpe).IsObjectOrPointer())) {
            if ((m).dtor_wasFunction) {
              _1309_tpe = RAST.__default.SelfBorrowed;
            } else {
              _1309_tpe = RAST.__default.SelfBorrowedMut;
            }
          } else {
            if (!((_1309_tpe).CanReadWithoutClone())) {
              _1309_tpe = RAST.Type.create_Borrowed(_1309_tpe);
            }
          }
          _1298_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1307_selfId, _1309_tpe)), _1298_params);
        }
        _1306_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1307_selfId);
      }
      Dafny.ISequence<RAST._IType> _1310_retTypeArgs;
      _1310_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1311_typeI;
      _1311_typeI = BigInteger.Zero;
      while ((_1311_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1312_typeExpr;
        RAST._IType _out97;
        _out97 = (this).GenType(((m).dtor_outTypes).Select(_1311_typeI), false, false);
        _1312_typeExpr = _out97;
        _1310_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1310_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1312_typeExpr));
        _1311_typeI = (_1311_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1313_visibility;
      _1313_visibility = ((forTrait) ? (RAST.Visibility.create_PRIV()) : (RAST.Visibility.create_PUB()));
      Dafny.ISequence<DAST._ITypeArgDecl> _1314_typeParamsFiltered;
      _1314_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi24 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1315_typeParamI = BigInteger.Zero; _1315_typeParamI < _hi24; _1315_typeParamI++) {
        DAST._ITypeArgDecl _1316_typeParam;
        _1316_typeParam = ((m).dtor_typeParams).Select(_1315_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1316_typeParam).dtor_name)))) {
          _1314_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1314_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1316_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1317_typeParams;
      _1317_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1314_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi25 = new BigInteger((_1314_typeParamsFiltered).Count);
        for (BigInteger _1318_i = BigInteger.Zero; _1318_i < _hi25; _1318_i++) {
          DAST._IType _1319_typeArg;
          RAST._ITypeParamDecl _1320_rTypeParamDecl;
          DAST._IType _out98;
          RAST._ITypeParamDecl _out99;
          (this).GenTypeParam((_1314_typeParamsFiltered).Select(_1318_i), out _out98, out _out99);
          _1319_typeArg = _out98;
          _1320_rTypeParamDecl = _out99;
          var _pat_let_tv104 = _1320_rTypeParamDecl;
          _1320_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1320_rTypeParamDecl, _pat_let9_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let9_0, _1321_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Dafny.Sequence<RAST._IType>.Concat((_pat_let_tv104).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default")))), _pat_let10_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let10_0, _1322_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1321_dt__update__tmp_h0).dtor_content, _1322_dt__update_hconstraints_h0)))));
          _1317_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1317_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1320_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1323_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1324_env = DCOMP.Environment.Default();
      RAST._IExpr _1325_preBody;
      _1325_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1326_preAssignNames;
      _1326_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1327_preAssignTypes;
      _1327_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        RAST._IExpr _1328_earlyReturn;
        _1328_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source59 = (m).dtor_outVars;
        bool unmatched59 = true;
        if (unmatched59) {
          if (_source59.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1329_outVars = _source59.dtor_value;
            unmatched59 = false;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1328_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(Dafny.Sequence<RAST._IExpr>.FromElements())));
                BigInteger _hi26 = new BigInteger((_1329_outVars).Count);
                for (BigInteger _1330_outI = BigInteger.Zero; _1330_outI < _hi26; _1330_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1331_outVar;
                  _1331_outVar = (_1329_outVars).Select(_1330_outI);
                  Dafny.ISequence<Dafny.Rune> _1332_outName;
                  _1332_outName = DCOMP.__default.escapeName((_1331_outVar));
                  Dafny.ISequence<Dafny.Rune> _1333_tracker__name;
                  _1333_tracker__name = DCOMP.__default.AddAssignedPrefix(_1332_outName);
                  _1326_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1326_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1333_tracker__name));
                  _1327_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1327_preAssignTypes, _1333_tracker__name, RAST.Type.create_Bool());
                  _1325_preBody = (_1325_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1333_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<RAST._IExpr> _1334_tupleArgs;
                _1334_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
                BigInteger _hi27 = new BigInteger((_1329_outVars).Count);
                for (BigInteger _1335_outI = BigInteger.Zero; _1335_outI < _hi27; _1335_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1336_outVar;
                  _1336_outVar = (_1329_outVars).Select(_1335_outI);
                  RAST._IType _1337_outType;
                  RAST._IType _out100;
                  _out100 = (this).GenType(((m).dtor_outTypes).Select(_1335_outI), false, false);
                  _1337_outType = _out100;
                  Dafny.ISequence<Dafny.Rune> _1338_outName;
                  _1338_outName = DCOMP.__default.escapeName((_1336_outVar));
                  _1299_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1299_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1338_outName));
                  RAST._IType _1339_outMaybeType;
                  _1339_outMaybeType = (((_1337_outType).CanReadWithoutClone()) ? (_1337_outType) : (RAST.__default.MaybePlaceboType(_1337_outType)));
                  _1300_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1300_paramTypes, _1338_outName, _1339_outMaybeType);
                  RAST._IExpr _1340_outVarReturn;
                  DCOMP._IOwnership _1341___v59;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1342___v60;
                  RAST._IExpr _out101;
                  DCOMP._IOwnership _out102;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out103;
                  (this).GenExpr(DAST.Expression.create_Ident((_1336_outVar)), Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1338_outName), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>, RAST._IType>(_1338_outName, _1339_outMaybeType))), DCOMP.Ownership.create_OwnershipOwned(), out _out101, out _out102, out _out103);
                  _1340_outVarReturn = _out101;
                  _1341___v59 = _out102;
                  _1342___v60 = _out103;
                  _1334_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1334_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1340_outVarReturn));
                }
                if ((new BigInteger((_1334_tupleArgs).Count)) == (BigInteger.One)) {
                  _1328_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1334_tupleArgs).Select(BigInteger.Zero)));
                } else {
                  _1328_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1334_tupleArgs)));
                }
              }
            }
          }
        }
        if (unmatched59) {
          unmatched59 = false;
        }
        _1324_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1326_preAssignNames, _1299_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1327_preAssignTypes, _1300_paramTypes));
        RAST._IExpr _1343_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1344___v61;
        DCOMP._IEnvironment _1345___v62;
        RAST._IExpr _out104;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out105;
        DCOMP._IEnvironment _out106;
        (this).GenStmts((m).dtor_body, _1306_selfIdentifier, _1324_env, true, _1328_earlyReturn, out _out104, out _out105, out _out106);
        _1343_body = _out104;
        _1344___v61 = _out105;
        _1345___v62 = _out106;
        _1323_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1325_preBody).Then(_1343_body));
      } else {
        _1324_env = DCOMP.Environment.create(_1299_paramNames, _1300_paramTypes);
        _1323_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1313_visibility, RAST.Fn.create(_1305_fnName, _1317_typeParams, _1298_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1310_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1310_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1310_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1323_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1346_declarations;
      _1346_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1347_i;
      _1347_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1348_stmts;
      _1348_stmts = stmts;
      while ((_1347_i) < (new BigInteger((_1348_stmts).Count))) {
        DAST._IStatement _1349_stmt;
        _1349_stmt = (_1348_stmts).Select(_1347_i);
        DAST._IStatement _source60 = _1349_stmt;
        bool unmatched60 = true;
        if (unmatched60) {
          if (_source60.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1350_name = _source60.dtor_name;
            DAST._IType _1351_optType = _source60.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source60.dtor_maybeValue;
            if (maybeValue0.is_None) {
              unmatched60 = false;
              if (((_1347_i) + (BigInteger.One)) < (new BigInteger((_1348_stmts).Count))) {
                DAST._IStatement _source61 = (_1348_stmts).Select((_1347_i) + (BigInteger.One));
                bool unmatched61 = true;
                if (unmatched61) {
                  if (_source61.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source61.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> ident0 = lhs0.dtor_ident;
                      Dafny.ISequence<Dafny.Rune> _1352_name2 = ident0;
                      DAST._IExpression _1353_rhs = _source61.dtor_value;
                      unmatched61 = false;
                      if (object.Equals(_1352_name2, _1350_name)) {
                        _1348_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1348_stmts).Subsequence(BigInteger.Zero, _1347_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1350_name, _1351_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1353_rhs)))), (_1348_stmts).Drop((_1347_i) + (BigInteger.One)));
                        _1349_stmt = (_1348_stmts).Select(_1347_i);
                      }
                    }
                  }
                }
                if (unmatched61) {
                  DAST._IStatement _1354___v63 = _source61;
                  unmatched61 = false;
                }
              }
            }
          }
        }
        if (unmatched60) {
          DAST._IStatement _1355___v64 = _source60;
          unmatched60 = false;
        }
        RAST._IExpr _1356_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1357_recIdents;
        DCOMP._IEnvironment _1358_newEnv2;
        RAST._IExpr _out107;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out108;
        DCOMP._IEnvironment _out109;
        (this).GenStmt(_1349_stmt, selfIdent, newEnv, (isLast) && ((_1347_i) == ((new BigInteger((_1348_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out107, out _out108, out _out109);
        _1356_stmtExpr = _out107;
        _1357_recIdents = _out108;
        _1358_newEnv2 = _out109;
        newEnv = _1358_newEnv2;
        DAST._IStatement _source62 = _1349_stmt;
        bool unmatched62 = true;
        if (unmatched62) {
          if (_source62.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1359_name = _source62.dtor_name;
            DAST._IType _1360___v65 = _source62.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> _1361___v66 = _source62.dtor_maybeValue;
            unmatched62 = false;
            {
              _1346_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1346_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_1359_name)));
            }
          }
        }
        if (unmatched62) {
          DAST._IStatement _1362___v67 = _source62;
          unmatched62 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1357_recIdents, _1346_declarations));
        generated = (generated).Then(_1356_stmtExpr);
        _1347_i = (_1347_i) + (BigInteger.One);
      }
    }
    public void GenAssignLhs(DAST._IAssignLhs lhs, RAST._IExpr rhs, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, out RAST._IExpr generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      newEnv = env;
      DAST._IAssignLhs _source63 = lhs;
      bool unmatched63 = true;
      if (unmatched63) {
        if (_source63.is_Ident) {
          Dafny.ISequence<Dafny.Rune> ident1 = _source63.dtor_ident;
          Dafny.ISequence<Dafny.Rune> _1363_id = ident1;
          unmatched63 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1364_idRust;
            _1364_idRust = DCOMP.__default.escapeName(_1363_id);
            if (((env).IsBorrowed(_1364_idRust)) || ((env).IsBorrowedMut(_1364_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1364_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1364_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1364_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Select) {
          DAST._IExpression _1365_on = _source63.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1366_field = _source63.dtor_field;
          unmatched63 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1367_fieldName;
            _1367_fieldName = DCOMP.__default.escapeName(_1366_field);
            RAST._IExpr _1368_onExpr;
            DCOMP._IOwnership _1369_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1370_recIdents;
            RAST._IExpr _out110;
            DCOMP._IOwnership _out111;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out112;
            (this).GenExpr(_1365_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out110, out _out111, out _out112);
            _1368_onExpr = _out110;
            _1369_onOwned = _out111;
            _1370_recIdents = _out112;
            generated = RAST.__default.AssignMember(_1368_onExpr, _1367_fieldName, rhs);
            RAST._IExpr _source64 = _1368_onExpr;
            bool unmatched64 = true;
            if (unmatched64) {
              bool disjunctiveMatch9 = false;
              if (_source64.is_UnaryOp) {
                Dafny.ISequence<Dafny.Rune> op15 = _source64.dtor_op1;
                if (object.Equals(op15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut"))) {
                  RAST._IExpr underlying5 = _source64.dtor_underlying;
                  if (underlying5.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name12 = underlying5.dtor_name;
                    if (object.Equals(name12, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      DAST.Format._IUnaryOpFormat _1371___v68 = _source64.dtor_format;
                      disjunctiveMatch9 = true;
                    }
                  }
                }
              }
              if (_source64.is_Identifier) {
                Dafny.ISequence<Dafny.Rune> name13 = _source64.dtor_name;
                if (object.Equals(name13, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                  disjunctiveMatch9 = true;
                }
              }
              if (disjunctiveMatch9) {
                unmatched64 = false;
                Dafny.ISequence<Dafny.Rune> _1372_isAssignedVar;
                _1372_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1367_fieldName);
                if (((newEnv).dtor_names).Contains(_1372_isAssignedVar)) {
                  generated = ((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1367_fieldName), RAST.Expr.create_Identifier(_1372_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1372_isAssignedVar);
                }
              }
            }
            if (unmatched64) {
              RAST._IExpr _1373___v69 = _source64;
              unmatched64 = false;
            }
            readIdents = _1370_recIdents;
            needsIIFE = false;
          }
        }
      }
      if (unmatched63) {
        DAST._IExpression _1374_on = _source63.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1375_indices = _source63.dtor_indices;
        unmatched63 = false;
        {
          RAST._IExpr _1376_onExpr;
          DCOMP._IOwnership _1377_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1378_recIdents;
          RAST._IExpr _out113;
          DCOMP._IOwnership _out114;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out115;
          (this).GenExpr(_1374_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out113, out _out114, out _out115);
          _1376_onExpr = _out113;
          _1377_onOwned = _out114;
          _1378_recIdents = _out115;
          readIdents = _1378_recIdents;
          _1376_onExpr = ((this).modify__macro).Apply1(_1376_onExpr);
          RAST._IExpr _1379_r;
          _1379_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1380_indicesExpr;
          _1380_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi28 = new BigInteger((_1375_indices).Count);
          for (BigInteger _1381_i = BigInteger.Zero; _1381_i < _hi28; _1381_i++) {
            RAST._IExpr _1382_idx;
            DCOMP._IOwnership _1383___v70;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1384_recIdentsIdx;
            RAST._IExpr _out116;
            DCOMP._IOwnership _out117;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out118;
            (this).GenExpr((_1375_indices).Select(_1381_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out116, out _out117, out _out118);
            _1382_idx = _out116;
            _1383___v70 = _out117;
            _1384_recIdentsIdx = _out118;
            Dafny.ISequence<Dafny.Rune> _1385_varName;
            _1385_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1381_i));
            _1380_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1380_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1385_varName)));
            _1379_r = (_1379_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1385_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<usize as ::dafny_runtime::NumCast>::from("), (_1382_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"))))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1384_recIdentsIdx);
          }
          if ((new BigInteger((_1375_indices).Count)) > (BigInteger.One)) {
            _1376_onExpr = (_1376_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1386_rhs;
          _1386_rhs = rhs;
          var _pat_let_tv105 = env;
          if (((_1376_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1376_onExpr).LhsIdentifierName(), _pat_let11_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let11_0, _1387_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv105).GetType(_1387_name), _pat_let12_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let12_0, _1388_tpe => ((_1388_tpe).is_Some) && (((_1388_tpe).dtor_value).IsUninitArray())))))))) {
            _1386_rhs = RAST.__default.MaybeUninitNew(_1386_rhs);
          }
          generated = (_1379_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1376_onExpr, _1380_indicesExpr)), _1386_rhs));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source65 = stmt;
      bool unmatched65 = true;
      if (unmatched65) {
        if (_source65.is_ConstructorNewSeparator) {
          Dafny.ISequence<DAST._IFormal> _1389_fields = _source65.dtor_fields;
          unmatched65 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi29 = new BigInteger((_1389_fields).Count);
            for (BigInteger _1390_i = BigInteger.Zero; _1390_i < _hi29; _1390_i++) {
              DAST._IFormal _1391_field;
              _1391_field = (_1389_fields).Select(_1390_i);
              Dafny.ISequence<Dafny.Rune> _1392_fieldName;
              _1392_fieldName = DCOMP.__default.escapeName((_1391_field).dtor_name);
              RAST._IType _1393_fieldTyp;
              RAST._IType _out119;
              _out119 = (this).GenType((_1391_field).dtor_typ, false, false);
              _1393_fieldTyp = _out119;
              Dafny.ISequence<Dafny.Rune> _1394_isAssignedVar;
              _1394_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1392_fieldName);
              if (((newEnv).dtor_names).Contains(_1394_isAssignedVar)) {
                RAST._IExpr _1395_rhs;
                DCOMP._IOwnership _1396___v71;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1397___v72;
                RAST._IExpr _out120;
                DCOMP._IOwnership _out121;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out122;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1391_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out120, out _out121, out _out122);
                _1395_rhs = _out120;
                _1396___v71 = _out121;
                _1397___v72 = _out122;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1394_isAssignedVar));
                generated = (generated).Then(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_if_uninit!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1392_fieldName), RAST.Expr.create_Identifier(_1394_isAssignedVar), _1395_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1394_isAssignedVar);
              }
            }
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1398_name = _source65.dtor_name;
          DAST._IType _1399_typ = _source65.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source65.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1400_expression = maybeValue1.dtor_value;
            unmatched65 = false;
            {
              RAST._IType _1401_tpe;
              RAST._IType _out123;
              _out123 = (this).GenType(_1399_typ, true, false);
              _1401_tpe = _out123;
              Dafny.ISequence<Dafny.Rune> _1402_varName;
              _1402_varName = DCOMP.__default.escapeName(_1398_name);
              bool _1403_hasCopySemantics;
              _1403_hasCopySemantics = (_1401_tpe).CanReadWithoutClone();
              if (((_1400_expression).is_InitializationValue) && (!(_1403_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1402_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).ApplyType1(_1401_tpe)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1402_varName, RAST.__default.MaybePlaceboType(_1401_tpe));
              } else {
                RAST._IExpr _1404_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1405_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1400_expression).is_InitializationValue) && ((_1401_tpe).IsObjectOrPointer())) {
                  _1404_expr = (_1401_tpe).ToNullExpr();
                  _1405_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1406_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out124;
                  DCOMP._IOwnership _out125;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
                  (this).GenExpr(_1400_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out124, out _out125, out _out126);
                  _1404_expr = _out124;
                  _1406_exprOwnership = _out125;
                  _1405_recIdents = _out126;
                }
                readIdents = _1405_recIdents;
                _1401_tpe = (((_1400_expression).is_NewUninitArray) ? ((_1401_tpe).TypeAtInitialization()) : (_1401_tpe));
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_1398_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1401_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1404_expr));
                newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_1398_name), _1401_tpe);
              }
            }
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1407_name = _source65.dtor_name;
          DAST._IType _1408_typ = _source65.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source65.dtor_maybeValue;
          if (maybeValue2.is_None) {
            unmatched65 = false;
            {
              DAST._IStatement _1409_newStmt;
              _1409_newStmt = DAST.Statement.create_DeclareVar(_1407_name, _1408_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1408_typ)));
              RAST._IExpr _out127;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out128;
              DCOMP._IEnvironment _out129;
              (this).GenStmt(_1409_newStmt, selfIdent, env, isLast, earlyReturn, out _out127, out _out128, out _out129);
              generated = _out127;
              readIdents = _out128;
              newEnv = _out129;
            }
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_Assign) {
          DAST._IAssignLhs _1410_lhs = _source65.dtor_lhs;
          DAST._IExpression _1411_expression = _source65.dtor_value;
          unmatched65 = false;
          {
            RAST._IExpr _1412_exprGen;
            DCOMP._IOwnership _1413___v73;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1414_exprIdents;
            RAST._IExpr _out130;
            DCOMP._IOwnership _out131;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out132;
            (this).GenExpr(_1411_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out130, out _out131, out _out132);
            _1412_exprGen = _out130;
            _1413___v73 = _out131;
            _1414_exprIdents = _out132;
            if ((_1410_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1415_rustId;
              _1415_rustId = DCOMP.__default.escapeName(((_1410_lhs).dtor_ident));
              Std.Wrappers._IOption<RAST._IType> _1416_tpe;
              _1416_tpe = (env).GetType(_1415_rustId);
              if (((_1416_tpe).is_Some) && ((((_1416_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1412_exprGen = RAST.__default.MaybePlacebo(_1412_exprGen);
              }
            }
            RAST._IExpr _1417_lhsGen;
            bool _1418_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1419_recIdents;
            DCOMP._IEnvironment _1420_resEnv;
            RAST._IExpr _out133;
            bool _out134;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
            DCOMP._IEnvironment _out136;
            (this).GenAssignLhs(_1410_lhs, _1412_exprGen, selfIdent, env, out _out133, out _out134, out _out135, out _out136);
            _1417_lhsGen = _out133;
            _1418_needsIIFE = _out134;
            _1419_recIdents = _out135;
            _1420_resEnv = _out136;
            generated = _1417_lhsGen;
            newEnv = _1420_resEnv;
            if (_1418_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1419_recIdents, _1414_exprIdents);
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_If) {
          DAST._IExpression _1421_cond = _source65.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1422_thnDafny = _source65.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1423_elsDafny = _source65.dtor_els;
          unmatched65 = false;
          {
            RAST._IExpr _1424_cond;
            DCOMP._IOwnership _1425___v74;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1426_recIdents;
            RAST._IExpr _out137;
            DCOMP._IOwnership _out138;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out139;
            (this).GenExpr(_1421_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out137, out _out138, out _out139);
            _1424_cond = _out137;
            _1425___v74 = _out138;
            _1426_recIdents = _out139;
            Dafny.ISequence<Dafny.Rune> _1427_condString;
            _1427_condString = (_1424_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1426_recIdents;
            RAST._IExpr _1428_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1429_thnIdents;
            DCOMP._IEnvironment _1430_thnEnv;
            RAST._IExpr _out140;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out141;
            DCOMP._IEnvironment _out142;
            (this).GenStmts(_1422_thnDafny, selfIdent, env, isLast, earlyReturn, out _out140, out _out141, out _out142);
            _1428_thn = _out140;
            _1429_thnIdents = _out141;
            _1430_thnEnv = _out142;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1429_thnIdents);
            RAST._IExpr _1431_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1432_elsIdents;
            DCOMP._IEnvironment _1433_elsEnv;
            RAST._IExpr _out143;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
            DCOMP._IEnvironment _out145;
            (this).GenStmts(_1423_elsDafny, selfIdent, env, isLast, earlyReturn, out _out143, out _out144, out _out145);
            _1431_els = _out143;
            _1432_elsIdents = _out144;
            _1433_elsEnv = _out145;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1432_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1424_cond, _1428_thn, _1431_els);
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1434_lbl = _source65.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1435_body = _source65.dtor_body;
          unmatched65 = false;
          {
            RAST._IExpr _1436_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1437_bodyIdents;
            DCOMP._IEnvironment _1438_env2;
            RAST._IExpr _out146;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out147;
            DCOMP._IEnvironment _out148;
            (this).GenStmts(_1435_body, selfIdent, env, isLast, earlyReturn, out _out146, out _out147, out _out148);
            _1436_body = _out146;
            _1437_bodyIdents = _out147;
            _1438_env2 = _out148;
            readIdents = _1437_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1434_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1436_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_While) {
          DAST._IExpression _1439_cond = _source65.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1440_body = _source65.dtor_body;
          unmatched65 = false;
          {
            RAST._IExpr _1441_cond;
            DCOMP._IOwnership _1442___v75;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1443_recIdents;
            RAST._IExpr _out149;
            DCOMP._IOwnership _out150;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out151;
            (this).GenExpr(_1439_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out149, out _out150, out _out151);
            _1441_cond = _out149;
            _1442___v75 = _out150;
            _1443_recIdents = _out151;
            readIdents = _1443_recIdents;
            RAST._IExpr _1444_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1445_bodyIdents;
            DCOMP._IEnvironment _1446_bodyEnv;
            RAST._IExpr _out152;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out153;
            DCOMP._IEnvironment _out154;
            (this).GenStmts(_1440_body, selfIdent, env, false, earlyReturn, out _out152, out _out153, out _out154);
            _1444_bodyExpr = _out152;
            _1445_bodyIdents = _out153;
            _1446_bodyEnv = _out154;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1445_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1441_cond), _1444_bodyExpr);
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1447_boundName = _source65.dtor_boundName;
          DAST._IType _1448_boundType = _source65.dtor_boundType;
          DAST._IExpression _1449_over = _source65.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1450_body = _source65.dtor_body;
          unmatched65 = false;
          {
            RAST._IExpr _1451_over;
            DCOMP._IOwnership _1452___v76;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1453_recIdents;
            RAST._IExpr _out155;
            DCOMP._IOwnership _out156;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out157;
            (this).GenExpr(_1449_over, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out155, out _out156, out _out157);
            _1451_over = _out155;
            _1452___v76 = _out156;
            _1453_recIdents = _out157;
            RAST._IType _1454_boundTpe;
            RAST._IType _out158;
            _out158 = (this).GenType(_1448_boundType, false, false);
            _1454_boundTpe = _out158;
            readIdents = _1453_recIdents;
            Dafny.ISequence<Dafny.Rune> _1455_boundRName;
            _1455_boundRName = DCOMP.__default.escapeName(_1447_boundName);
            RAST._IExpr _1456_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1457_bodyIdents;
            DCOMP._IEnvironment _1458_bodyEnv;
            RAST._IExpr _out159;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out160;
            DCOMP._IEnvironment _out161;
            (this).GenStmts(_1450_body, selfIdent, (env).AddAssigned(_1455_boundRName, _1454_boundTpe), false, earlyReturn, out _out159, out _out160, out _out161);
            _1456_bodyExpr = _out159;
            _1457_bodyIdents = _out160;
            _1458_bodyEnv = _out161;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1457_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1455_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1455_boundRName, _1451_over, _1456_bodyExpr);
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1459_toLabel = _source65.dtor_toLabel;
          unmatched65 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source66 = _1459_toLabel;
            bool unmatched66 = true;
            if (unmatched66) {
              if (_source66.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1460_lbl = _source66.dtor_value;
                unmatched66 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1460_lbl)));
                }
              }
            }
            if (unmatched66) {
              unmatched66 = false;
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1461_body = _source65.dtor_body;
          unmatched65 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
            }
            newEnv = env;
            BigInteger _hi30 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1462_paramI = BigInteger.Zero; _1462_paramI < _hi30; _1462_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1463_param;
              _1463_param = ((env).dtor_names).Select(_1462_paramI);
              RAST._IExpr _1464_paramInit;
              DCOMP._IOwnership _1465___v77;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1466___v78;
              RAST._IExpr _out162;
              DCOMP._IOwnership _out163;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out164;
              (this).GenIdent(_1463_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out162, out _out163, out _out164);
              _1464_paramInit = _out162;
              _1465___v77 = _out163;
              _1466___v78 = _out164;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1463_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1464_paramInit)));
              if (((env).dtor_types).Contains(_1463_param)) {
                RAST._IType _1467_declaredType;
                _1467_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1463_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1463_param, _1467_declaredType);
              }
            }
            RAST._IExpr _1468_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1469_bodyIdents;
            DCOMP._IEnvironment _1470_bodyEnv;
            RAST._IExpr _out165;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out166;
            DCOMP._IEnvironment _out167;
            (this).GenStmts(_1461_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), newEnv, false, earlyReturn, out _out165, out _out166, out _out167);
            _1468_bodyExpr = _out165;
            _1469_bodyIdents = _out166;
            _1470_bodyEnv = _out167;
            readIdents = _1469_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1468_bodyExpr)));
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_JumpTailCallStart) {
          unmatched65 = false;
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_Call) {
          DAST._IExpression _1471_on = _source65.dtor_on;
          DAST._ICallName _1472_name = _source65.dtor_callName;
          Dafny.ISequence<DAST._IType> _1473_typeArgs = _source65.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1474_args = _source65.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1475_maybeOutVars = _source65.dtor_outs;
          unmatched65 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IExpr _1476_onExpr;
            DCOMP._IOwnership _1477___v79;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1478_enclosingIdents;
            RAST._IExpr _out168;
            DCOMP._IOwnership _out169;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out170;
            (this).GenExpr(_1471_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out168, out _out169, out _out170);
            _1476_onExpr = _out168;
            _1477___v79 = _out169;
            _1478_enclosingIdents = _out170;
            Dafny.ISequence<RAST._IType> _1479_typeArgsR;
            _1479_typeArgsR = Dafny.Sequence<RAST._IType>.FromElements();
            if ((new BigInteger((_1473_typeArgs).Count)) >= (BigInteger.One)) {
              BigInteger _1480_typeI;
              _1480_typeI = BigInteger.Zero;
              while ((_1480_typeI) < (new BigInteger((_1473_typeArgs).Count))) {
                RAST._IType _1481_tpe;
                RAST._IType _out171;
                _out171 = (this).GenType((_1473_typeArgs).Select(_1480_typeI), false, false);
                _1481_tpe = _out171;
                _1479_typeArgsR = Dafny.Sequence<RAST._IType>.Concat(_1479_typeArgsR, Dafny.Sequence<RAST._IType>.FromElements(_1481_tpe));
                _1480_typeI = (_1480_typeI) + (BigInteger.One);
              }
            }
            Dafny.ISequence<RAST._IExpr> _1482_argExprs;
            _1482_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi31 = new BigInteger((_1474_args).Count);
            for (BigInteger _1483_i = BigInteger.Zero; _1483_i < _hi31; _1483_i++) {
              DCOMP._IOwnership _1484_argOwnership;
              _1484_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              if (((_1472_name).is_CallName) && ((_1483_i) < (new BigInteger((((_1472_name).dtor_signature)).Count)))) {
                RAST._IType _1485_tpe;
                RAST._IType _out172;
                _out172 = (this).GenType(((((_1472_name).dtor_signature)).Select(_1483_i)).dtor_typ, false, false);
                _1485_tpe = _out172;
                if ((_1485_tpe).CanReadWithoutClone()) {
                  _1484_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
                }
              }
              RAST._IExpr _1486_argExpr;
              DCOMP._IOwnership _1487_ownership;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1488_argIdents;
              RAST._IExpr _out173;
              DCOMP._IOwnership _out174;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out175;
              (this).GenExpr((_1474_args).Select(_1483_i), selfIdent, env, _1484_argOwnership, out _out173, out _out174, out _out175);
              _1486_argExpr = _out173;
              _1487_ownership = _out174;
              _1488_argIdents = _out175;
              _1482_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1482_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1486_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1488_argIdents);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1478_enclosingIdents);
            Dafny.ISequence<Dafny.Rune> _1489_renderedName;
            _1489_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
              DAST._ICallName _source67 = _1472_name;
              bool unmatched67 = true;
              if (unmatched67) {
                if (_source67.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _1490_name = _source67.dtor_name;
                  Std.Wrappers._IOption<DAST._IType> _1491___v80 = _source67.dtor_onType;
                  Dafny.ISequence<DAST._IFormal> _1492___v81 = _source67.dtor_signature;
                  unmatched67 = false;
                  return DCOMP.__default.escapeName(_1490_name);
                }
              }
              if (unmatched67) {
                bool disjunctiveMatch10 = false;
                if (_source67.is_MapBuilderAdd) {
                  disjunctiveMatch10 = true;
                }
                if (_source67.is_SetBuilderAdd) {
                  disjunctiveMatch10 = true;
                }
                if (disjunctiveMatch10) {
                  unmatched67 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                }
              }
              if (unmatched67) {
                bool disjunctiveMatch11 = false;
                disjunctiveMatch11 = true;
                disjunctiveMatch11 = true;
                if (disjunctiveMatch11) {
                  unmatched67 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                }
              }
              throw new System.Exception("unexpected control point");
            }))();
            DAST._IExpression _source68 = _1471_on;
            bool unmatched68 = true;
            if (unmatched68) {
              if (_source68.is_Companion) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1493___v82 = _source68.dtor_Companion_a0;
                unmatched68 = false;
                {
                  _1476_onExpr = (_1476_onExpr).MSel(_1489_renderedName);
                }
              }
            }
            if (unmatched68) {
              DAST._IExpression _1494___v83 = _source68;
              unmatched68 = false;
              {
                DAST._ICallName _source69 = _1472_name;
                bool unmatched69 = true;
                if (unmatched69) {
                  if (_source69.is_CallName) {
                    Dafny.ISequence<Dafny.Rune> _1495___v84 = _source69.dtor_name;
                    Std.Wrappers._IOption<DAST._IType> onType0 = _source69.dtor_onType;
                    if (onType0.is_Some) {
                      DAST._IType _1496_tpe = onType0.dtor_value;
                      Dafny.ISequence<DAST._IFormal> _1497___v85 = _source69.dtor_signature;
                      unmatched69 = false;
                      RAST._IType _1498_typ;
                      RAST._IType _out176;
                      _out176 = (this).GenType(_1496_tpe, false, false);
                      _1498_typ = _out176;
                      if ((_1498_typ).IsObjectOrPointer()) {
                        _1476_onExpr = ((this).modify__macro).Apply1(_1476_onExpr);
                      }
                    }
                  }
                }
                if (unmatched69) {
                  DAST._ICallName _1499___v86 = _source69;
                  unmatched69 = false;
                }
                _1476_onExpr = (_1476_onExpr).Sel(_1489_renderedName);
              }
            }
            generated = _1476_onExpr;
            if ((new BigInteger((_1479_typeArgsR).Count)).Sign == 1) {
              generated = (generated).ApplyType(_1479_typeArgsR);
            }
            generated = (generated).Apply(_1482_argExprs);
            if (((_1475_maybeOutVars).is_Some) && ((new BigInteger(((_1475_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1500_outVar;
              _1500_outVar = DCOMP.__default.escapeName((((_1475_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
              if (!((env).CanReadWithoutClone(_1500_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1500_outVar, generated);
            } else if (((_1475_maybeOutVars).is_None) || ((new BigInteger(((_1475_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1501_tmpVar;
              _1501_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1502_tmpId;
              _1502_tmpId = RAST.Expr.create_Identifier(_1501_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1501_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1503_outVars;
              _1503_outVars = (_1475_maybeOutVars).dtor_value;
              BigInteger _hi32 = new BigInteger((_1503_outVars).Count);
              for (BigInteger _1504_outI = BigInteger.Zero; _1504_outI < _hi32; _1504_outI++) {
                Dafny.ISequence<Dafny.Rune> _1505_outVar;
                _1505_outVar = DCOMP.__default.escapeName(((_1503_outVars).Select(_1504_outI)));
                RAST._IExpr _1506_rhs;
                _1506_rhs = (_1502_tmpId).Sel(Std.Strings.__default.OfNat(_1504_outI));
                if (!((env).CanReadWithoutClone(_1505_outVar))) {
                  _1506_rhs = RAST.__default.MaybePlacebo(_1506_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1505_outVar, _1506_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_Return) {
          DAST._IExpression _1507_exprDafny = _source65.dtor_expr;
          unmatched65 = false;
          {
            RAST._IExpr _1508_expr;
            DCOMP._IOwnership _1509___v87;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1510_recIdents;
            RAST._IExpr _out177;
            DCOMP._IOwnership _out178;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out179;
            (this).GenExpr(_1507_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out177, out _out178, out _out179);
            _1508_expr = _out177;
            _1509___v87 = _out178;
            _1510_recIdents = _out179;
            readIdents = _1510_recIdents;
            if (isLast) {
              generated = _1508_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1508_expr));
            }
            newEnv = env;
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_EarlyReturn) {
          unmatched65 = false;
          {
            generated = earlyReturn;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_Halt) {
          unmatched65 = false;
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched65) {
        DAST._IExpression _1511_e = _source65.dtor_Print_a0;
        unmatched65 = false;
        {
          RAST._IExpr _1512_printedExpr;
          DCOMP._IOwnership _1513_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1514_recIdents;
          RAST._IExpr _out180;
          DCOMP._IOwnership _out181;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out182;
          (this).GenExpr(_1511_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out180, out _out181, out _out182);
          _1512_printedExpr = _out180;
          _1513_recOwnership = _out181;
          _1514_recIdents = _out182;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1512_printedExpr)));
          readIdents = _1514_recIdents;
          newEnv = env;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source70 = range;
      bool unmatched70 = true;
      if (unmatched70) {
        if (_source70.is_NoRange) {
          unmatched70 = false;
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      if (unmatched70) {
        if (_source70.is_U8) {
          unmatched70 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      if (unmatched70) {
        if (_source70.is_U16) {
          unmatched70 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      if (unmatched70) {
        if (_source70.is_U32) {
          unmatched70 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      if (unmatched70) {
        if (_source70.is_U64) {
          unmatched70 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      if (unmatched70) {
        if (_source70.is_U128) {
          unmatched70 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      if (unmatched70) {
        if (_source70.is_I8) {
          unmatched70 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      if (unmatched70) {
        if (_source70.is_I16) {
          unmatched70 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      if (unmatched70) {
        if (_source70.is_I32) {
          unmatched70 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      if (unmatched70) {
        if (_source70.is_I64) {
          unmatched70 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      if (unmatched70) {
        if (_source70.is_I128) {
          unmatched70 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
        }
      }
      if (unmatched70) {
        DAST._INewtypeRange _1515___v88 = _source70;
        unmatched70 = false;
        return Std.Wrappers.Option<RAST._IType>.create_None();
      }
      throw new System.Exception("unexpected control point");
    }
    public static void FromOwned(RAST._IExpr r, DCOMP._IOwnership expectedOwnership, out RAST._IExpr @out, out DCOMP._IOwnership resultingOwnership)
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
        @out = RAST.__default.BorrowMut(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      }
    }
    public static void FromOwnership(RAST._IExpr r, DCOMP._IOwnership ownership, DCOMP._IOwnership expectedOwnership, out RAST._IExpr @out, out DCOMP._IOwnership resultingOwnership)
    {
      @out = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      if (object.Equals(ownership, expectedOwnership)) {
        @out = r;
        resultingOwnership = expectedOwnership;
        return ;
      }
      if (object.Equals(ownership, DCOMP.Ownership.create_OwnershipOwned())) {
        RAST._IExpr _out183;
        DCOMP._IOwnership _out184;
        DCOMP.COMP.FromOwned(r, expectedOwnership, out _out183, out _out184);
        @out = _out183;
        resultingOwnership = _out184;
        return ;
      } else if (object.Equals(ownership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        RAST._IExpr _out185;
        DCOMP._IOwnership _out186;
        DCOMP.COMP.FromOwned(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), r, DAST.Format.UnaryOpFormat.create_NoFormat()), expectedOwnership, out _out185, out _out186);
        @out = _out185;
        resultingOwnership = _out186;
      } else if ((object.Equals(ownership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(ownership, DCOMP.Ownership.create_OwnershipBorrowedMut()))) {
        if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
          @out = RAST.__default.Clone(r);
        } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
          @out = RAST.__default.BoxNew(RAST.__default.Clone(r));
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
    public void GenExprLiteral(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source71 = e;
      bool unmatched71 = true;
      if (unmatched71) {
        if (_source71.is_Literal) {
          DAST._ILiteral _h150 = _source71.dtor_Literal_a0;
          if (_h150.is_BoolLiteral) {
            bool _1516_b = _h150.dtor_BoolLiteral_a0;
            unmatched71 = false;
            {
              RAST._IExpr _out187;
              DCOMP._IOwnership _out188;
              DCOMP.COMP.FromOwned(RAST.Expr.create_LiteralBool(_1516_b), expectedOwnership, out _out187, out _out188);
              r = _out187;
              resultingOwnership = _out188;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_Literal) {
          DAST._ILiteral _h151 = _source71.dtor_Literal_a0;
          if (_h151.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1517_i = _h151.dtor_IntLiteral_a0;
            DAST._IType _1518_t = _h151.dtor_IntLiteral_a1;
            unmatched71 = false;
            {
              DAST._IType _source72 = _1518_t;
              bool unmatched72 = true;
              if (unmatched72) {
                if (_source72.is_Primitive) {
                  DAST._IPrimitive _h90 = _source72.dtor_Primitive_a0;
                  if (_h90.is_Int) {
                    unmatched72 = false;
                    {
                      if ((new BigInteger((_1517_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1517_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1517_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched72) {
                DAST._IType _1519_o = _source72;
                unmatched72 = false;
                {
                  RAST._IType _1520_genType;
                  RAST._IType _out189;
                  _out189 = (this).GenType(_1519_o, false, false);
                  _1520_genType = _out189;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1517_i), _1520_genType);
                }
              }
              RAST._IExpr _out190;
              DCOMP._IOwnership _out191;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out190, out _out191);
              r = _out190;
              resultingOwnership = _out191;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_Literal) {
          DAST._ILiteral _h152 = _source71.dtor_Literal_a0;
          if (_h152.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1521_n = _h152.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1522_d = _h152.dtor_DecLiteral_a1;
            DAST._IType _1523_t = _h152.dtor_DecLiteral_a2;
            unmatched71 = false;
            {
              DAST._IType _source73 = _1523_t;
              bool unmatched73 = true;
              if (unmatched73) {
                if (_source73.is_Primitive) {
                  DAST._IPrimitive _h91 = _source73.dtor_Primitive_a0;
                  if (_h91.is_Real) {
                    unmatched73 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1521_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1522_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched73) {
                DAST._IType _1524_o = _source73;
                unmatched73 = false;
                {
                  RAST._IType _1525_genType;
                  RAST._IType _out192;
                  _out192 = (this).GenType(_1524_o, false, false);
                  _1525_genType = _out192;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1521_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1522_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1525_genType);
                }
              }
              RAST._IExpr _out193;
              DCOMP._IOwnership _out194;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out193, out _out194);
              r = _out193;
              resultingOwnership = _out194;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_Literal) {
          DAST._ILiteral _h153 = _source71.dtor_Literal_a0;
          if (_h153.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1526_l = _h153.dtor_StringLiteral_a0;
            bool _1527_verbatim = _h153.dtor_verbatim;
            unmatched71 = false;
            {
              if (_1527_verbatim) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Verbatim strings prefixed by @ not supported yet."));
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1526_l, false, _1527_verbatim));
              RAST._IExpr _out195;
              DCOMP._IOwnership _out196;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out195, out _out196);
              r = _out195;
              resultingOwnership = _out196;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_Literal) {
          DAST._ILiteral _h154 = _source71.dtor_Literal_a0;
          if (_h154.is_CharLiteralUTF16) {
            BigInteger _1528_c = _h154.dtor_CharLiteralUTF16_a0;
            unmatched71 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1528_c));
              r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
              RAST._IExpr _out197;
              DCOMP._IOwnership _out198;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out197, out _out198);
              r = _out197;
              resultingOwnership = _out198;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_Literal) {
          DAST._ILiteral _h155 = _source71.dtor_Literal_a0;
          if (_h155.is_CharLiteral) {
            Dafny.Rune _1529_c = _h155.dtor_CharLiteral_a0;
            unmatched71 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1529_c).Value)));
              if (!((this).UnicodeChars)) {
                r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              } else {
                r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
              RAST._IExpr _out199;
              DCOMP._IOwnership _out200;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out199, out _out200);
              r = _out199;
              resultingOwnership = _out200;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched71) {
        DAST._ILiteral _h156 = _source71.dtor_Literal_a0;
        DAST._IType _1530_tpe = _h156.dtor_Null_a0;
        unmatched71 = false;
        {
          RAST._IType _1531_tpeGen;
          RAST._IType _out201;
          _out201 = (this).GenType(_1530_tpe, false, false);
          _1531_tpeGen = _out201;
          r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None")), _1531_tpeGen);
          RAST._IExpr _out202;
          DCOMP._IOwnership _out203;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out202, out _out203);
          r = _out202;
          resultingOwnership = _out203;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      }
    }
    public void GenExprBinary(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs52 = e;
      DAST._IBinOp _1532_op = _let_tmp_rhs52.dtor_op;
      DAST._IExpression _1533_lExpr = _let_tmp_rhs52.dtor_left;
      DAST._IExpression _1534_rExpr = _let_tmp_rhs52.dtor_right;
      DAST.Format._IBinaryOpFormat _1535_format = _let_tmp_rhs52.dtor_format2;
      bool _1536_becomesLeftCallsRight;
      _1536_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source74 = _1532_op;
        bool unmatched74 = true;
        if (unmatched74) {
          bool disjunctiveMatch12 = false;
          if (_source74.is_SetMerge) {
            disjunctiveMatch12 = true;
          }
          if (_source74.is_SetSubtraction) {
            disjunctiveMatch12 = true;
          }
          if (_source74.is_SetIntersection) {
            disjunctiveMatch12 = true;
          }
          if (_source74.is_SetDisjoint) {
            disjunctiveMatch12 = true;
          }
          if (_source74.is_MapMerge) {
            disjunctiveMatch12 = true;
          }
          if (_source74.is_MapSubtraction) {
            disjunctiveMatch12 = true;
          }
          if (_source74.is_MultisetMerge) {
            disjunctiveMatch12 = true;
          }
          if (_source74.is_MultisetSubtraction) {
            disjunctiveMatch12 = true;
          }
          if (_source74.is_MultisetIntersection) {
            disjunctiveMatch12 = true;
          }
          if (_source74.is_MultisetDisjoint) {
            disjunctiveMatch12 = true;
          }
          if (_source74.is_Concat) {
            disjunctiveMatch12 = true;
          }
          if (disjunctiveMatch12) {
            unmatched74 = false;
            return true;
          }
        }
        if (unmatched74) {
          DAST._IBinOp _1537___v89 = _source74;
          unmatched74 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1538_becomesRightCallsLeft;
      _1538_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source75 = _1532_op;
        bool unmatched75 = true;
        if (unmatched75) {
          if (_source75.is_In) {
            unmatched75 = false;
            return true;
          }
        }
        if (unmatched75) {
          DAST._IBinOp _1539___v90 = _source75;
          unmatched75 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1540_becomesCallLeftRight;
      _1540_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source76 = _1532_op;
        bool unmatched76 = true;
        if (unmatched76) {
          if (_source76.is_Eq) {
            bool referential0 = _source76.dtor_referential;
            if ((referential0) == (true)) {
              bool nullable0 = _source76.dtor_nullable;
              if ((nullable0) == (false)) {
                unmatched76 = false;
                return true;
              }
            }
          }
        }
        if (unmatched76) {
          if (_source76.is_SetMerge) {
            unmatched76 = false;
            return true;
          }
        }
        if (unmatched76) {
          if (_source76.is_SetSubtraction) {
            unmatched76 = false;
            return true;
          }
        }
        if (unmatched76) {
          if (_source76.is_SetIntersection) {
            unmatched76 = false;
            return true;
          }
        }
        if (unmatched76) {
          if (_source76.is_SetDisjoint) {
            unmatched76 = false;
            return true;
          }
        }
        if (unmatched76) {
          if (_source76.is_MapMerge) {
            unmatched76 = false;
            return true;
          }
        }
        if (unmatched76) {
          if (_source76.is_MapSubtraction) {
            unmatched76 = false;
            return true;
          }
        }
        if (unmatched76) {
          if (_source76.is_MultisetMerge) {
            unmatched76 = false;
            return true;
          }
        }
        if (unmatched76) {
          if (_source76.is_MultisetSubtraction) {
            unmatched76 = false;
            return true;
          }
        }
        if (unmatched76) {
          if (_source76.is_MultisetIntersection) {
            unmatched76 = false;
            return true;
          }
        }
        if (unmatched76) {
          if (_source76.is_MultisetDisjoint) {
            unmatched76 = false;
            return true;
          }
        }
        if (unmatched76) {
          if (_source76.is_Concat) {
            unmatched76 = false;
            return true;
          }
        }
        if (unmatched76) {
          DAST._IBinOp _1541___v91 = _source76;
          unmatched76 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      DCOMP._IOwnership _1542_expectedLeftOwnership;
      _1542_expectedLeftOwnership = ((_1536_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1538_becomesRightCallsLeft) || (_1540_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1543_expectedRightOwnership;
      _1543_expectedRightOwnership = (((_1536_becomesLeftCallsRight) || (_1540_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1538_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1544_left;
      DCOMP._IOwnership _1545___v92;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1546_recIdentsL;
      RAST._IExpr _out204;
      DCOMP._IOwnership _out205;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out206;
      (this).GenExpr(_1533_lExpr, selfIdent, env, _1542_expectedLeftOwnership, out _out204, out _out205, out _out206);
      _1544_left = _out204;
      _1545___v92 = _out205;
      _1546_recIdentsL = _out206;
      RAST._IExpr _1547_right;
      DCOMP._IOwnership _1548___v93;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1549_recIdentsR;
      RAST._IExpr _out207;
      DCOMP._IOwnership _out208;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out209;
      (this).GenExpr(_1534_rExpr, selfIdent, env, _1543_expectedRightOwnership, out _out207, out _out208, out _out209);
      _1547_right = _out207;
      _1548___v93 = _out208;
      _1549_recIdentsR = _out209;
      DAST._IBinOp _source77 = _1532_op;
      bool unmatched77 = true;
      if (unmatched77) {
        if (_source77.is_In) {
          unmatched77 = false;
          {
            r = ((_1547_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1544_left);
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_SeqProperPrefix) {
          unmatched77 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1544_left, _1547_right, _1535_format);
        }
      }
      if (unmatched77) {
        if (_source77.is_SeqPrefix) {
          unmatched77 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1544_left, _1547_right, _1535_format);
        }
      }
      if (unmatched77) {
        if (_source77.is_SetMerge) {
          unmatched77 = false;
          {
            r = ((_1544_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1547_right);
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_SetSubtraction) {
          unmatched77 = false;
          {
            r = ((_1544_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1547_right);
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_SetIntersection) {
          unmatched77 = false;
          {
            r = ((_1544_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1547_right);
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Subset) {
          unmatched77 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1544_left, _1547_right, _1535_format);
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_ProperSubset) {
          unmatched77 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1544_left, _1547_right, _1535_format);
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_SetDisjoint) {
          unmatched77 = false;
          {
            r = ((_1544_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1547_right);
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_MapMerge) {
          unmatched77 = false;
          {
            r = ((_1544_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1547_right);
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_MapSubtraction) {
          unmatched77 = false;
          {
            r = ((_1544_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1547_right);
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_MultisetMerge) {
          unmatched77 = false;
          {
            r = ((_1544_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1547_right);
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_MultisetSubtraction) {
          unmatched77 = false;
          {
            r = ((_1544_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1547_right);
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_MultisetIntersection) {
          unmatched77 = false;
          {
            r = ((_1544_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1547_right);
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Submultiset) {
          unmatched77 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1544_left, _1547_right, _1535_format);
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_ProperSubmultiset) {
          unmatched77 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1544_left, _1547_right, _1535_format);
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_MultisetDisjoint) {
          unmatched77 = false;
          {
            r = ((_1544_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1547_right);
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Concat) {
          unmatched77 = false;
          {
            r = ((_1544_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1547_right);
          }
        }
      }
      if (unmatched77) {
        DAST._IBinOp _1550___v94 = _source77;
        unmatched77 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1532_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1532_op), _1544_left, _1547_right, _1535_format);
          } else {
            DAST._IBinOp _source78 = _1532_op;
            bool unmatched78 = true;
            if (unmatched78) {
              if (_source78.is_Eq) {
                bool _1551_referential = _source78.dtor_referential;
                bool _1552_nullable = _source78.dtor_nullable;
                unmatched78 = false;
                {
                  if (_1551_referential) {
                    if (_1552_nullable) {
                      r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1544_left, _1547_right));
                    } else {
                      r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1544_left, _1547_right));
                    }
                  } else {
                    r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1544_left, _1547_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                  }
                }
              }
            }
            if (unmatched78) {
              if (_source78.is_EuclidianDiv) {
                unmatched78 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1544_left, _1547_right));
                }
              }
            }
            if (unmatched78) {
              if (_source78.is_EuclidianMod) {
                unmatched78 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1544_left, _1547_right));
                }
              }
            }
            if (unmatched78) {
              Dafny.ISequence<Dafny.Rune> _1553_op = _source78.dtor_Passthrough_a0;
              unmatched78 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1553_op, _1544_left, _1547_right, _1535_format);
              }
            }
          }
        }
      }
      RAST._IExpr _out210;
      DCOMP._IOwnership _out211;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out210, out _out211);
      r = _out210;
      resultingOwnership = _out211;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1546_recIdentsL, _1549_recIdentsR);
      return ;
    }
    public void GenExprConvertFromNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs53 = e;
      DAST._IExpression _1554_expr = _let_tmp_rhs53.dtor_value;
      DAST._IType _1555_fromTpe = _let_tmp_rhs53.dtor_from;
      DAST._IType _1556_toTpe = _let_tmp_rhs53.dtor_typ;
      RAST._IExpr _1557_recursiveGen;
      DCOMP._IOwnership _1558_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1559_recIdents;
      RAST._IExpr _out212;
      DCOMP._IOwnership _out213;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out214;
      (this).GenExpr(_1554_expr, selfIdent, env, expectedOwnership, out _out212, out _out213, out _out214);
      _1557_recursiveGen = _out212;
      _1558_recOwned = _out213;
      _1559_recIdents = _out214;
      r = _1557_recursiveGen;
      if (object.Equals(_1558_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      RAST._IExpr _out215;
      DCOMP._IOwnership _out216;
      DCOMP.COMP.FromOwnership(r, _1558_recOwned, expectedOwnership, out _out215, out _out216);
      r = _out215;
      resultingOwnership = _out216;
      readIdents = _1559_recIdents;
    }
    public void GenExprConvertToNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IExpression _1560_expr = _let_tmp_rhs54.dtor_value;
      DAST._IType _1561_fromTpe = _let_tmp_rhs54.dtor_from;
      DAST._IType _1562_toTpe = _let_tmp_rhs54.dtor_typ;
      RAST._IExpr _1563_recursiveGen;
      DCOMP._IOwnership _1564_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1565_recIdents;
      RAST._IExpr _out217;
      DCOMP._IOwnership _out218;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out219;
      (this).GenExpr(_1560_expr, selfIdent, env, expectedOwnership, out _out217, out _out218, out _out219);
      _1563_recursiveGen = _out217;
      _1564_recOwned = _out218;
      _1565_recIdents = _out219;
      r = _1563_recursiveGen;
      if (object.Equals(_1564_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
      RAST._IExpr _out220;
      DCOMP._IOwnership _out221;
      DCOMP.COMP.FromOwnership(r, _1564_recOwned, expectedOwnership, out _out220, out _out221);
      r = _out220;
      resultingOwnership = _out221;
      readIdents = _1565_recIdents;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _1566_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _1567_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _1568_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _1568_toTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1569___v95 = _let_tmp_rhs56.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _1570___v96 = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      DAST._IType _1571_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _1572_range = _let_tmp_rhs57.dtor_range;
      bool _1573_erase = _let_tmp_rhs57.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1574_attributes = _let_tmp_rhs57.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _1575_nativeToType;
      _1575_nativeToType = DCOMP.COMP.NewtypeToRustType(_1571_b, _1572_range);
      if (object.Equals(_1567_fromTpe, _1571_b)) {
        RAST._IExpr _1576_recursiveGen;
        DCOMP._IOwnership _1577_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1578_recIdents;
        RAST._IExpr _out222;
        DCOMP._IOwnership _out223;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out224;
        (this).GenExpr(_1566_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out222, out _out223, out _out224);
        _1576_recursiveGen = _out222;
        _1577_recOwned = _out223;
        _1578_recIdents = _out224;
        readIdents = _1578_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source79 = _1575_nativeToType;
        bool unmatched79 = true;
        if (unmatched79) {
          if (_source79.is_Some) {
            RAST._IType _1579_v = _source79.dtor_value;
            unmatched79 = false;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1576_recursiveGen, RAST.Expr.create_ExprFromType(_1579_v)));
            RAST._IExpr _out225;
            DCOMP._IOwnership _out226;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out225, out _out226);
            r = _out225;
            resultingOwnership = _out226;
          }
        }
        if (unmatched79) {
          unmatched79 = false;
          if (_1573_erase) {
            r = _1576_recursiveGen;
          } else {
            RAST._IType _1580_rhsType;
            RAST._IType _out227;
            _out227 = (this).GenType(_1568_toTpe, true, false);
            _1580_rhsType = _out227;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1580_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1576_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out228;
          DCOMP._IOwnership _out229;
          DCOMP.COMP.FromOwnership(r, _1577_recOwned, expectedOwnership, out _out228, out _out229);
          r = _out228;
          resultingOwnership = _out229;
        }
      } else {
        if ((_1575_nativeToType).is_Some) {
          DAST._IType _source80 = _1567_fromTpe;
          bool unmatched80 = true;
          if (unmatched80) {
            if (_source80.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1581___v97 = _source80.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _1582___v98 = _source80.dtor_typeArgs;
              DAST._IResolvedType resolved1 = _source80.dtor_resolved;
              if (resolved1.is_Newtype) {
                DAST._IType _1583_b0 = resolved1.dtor_baseType;
                DAST._INewtypeRange _1584_range0 = resolved1.dtor_range;
                bool _1585_erase0 = resolved1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1586_attributes0 = resolved1.dtor_attributes;
                unmatched80 = false;
                {
                  Std.Wrappers._IOption<RAST._IType> _1587_nativeFromType;
                  _1587_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1583_b0, _1584_range0);
                  if ((_1587_nativeFromType).is_Some) {
                    RAST._IExpr _1588_recursiveGen;
                    DCOMP._IOwnership _1589_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1590_recIdents;
                    RAST._IExpr _out230;
                    DCOMP._IOwnership _out231;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out232;
                    (this).GenExpr(_1566_expr, selfIdent, env, expectedOwnership, out _out230, out _out231, out _out232);
                    _1588_recursiveGen = _out230;
                    _1589_recOwned = _out231;
                    _1590_recIdents = _out232;
                    RAST._IExpr _out233;
                    DCOMP._IOwnership _out234;
                    DCOMP.COMP.FromOwnership(RAST.Expr.create_TypeAscription(_1588_recursiveGen, (_1575_nativeToType).dtor_value), _1589_recOwned, expectedOwnership, out _out233, out _out234);
                    r = _out233;
                    resultingOwnership = _out234;
                    readIdents = _1590_recIdents;
                    return ;
                  }
                }
              }
            }
          }
          if (unmatched80) {
            DAST._IType _1591___v99 = _source80;
            unmatched80 = false;
          }
          if (object.Equals(_1567_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1592_recursiveGen;
            DCOMP._IOwnership _1593_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1594_recIdents;
            RAST._IExpr _out235;
            DCOMP._IOwnership _out236;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out237;
            (this).GenExpr(_1566_expr, selfIdent, env, expectedOwnership, out _out235, out _out236, out _out237);
            _1592_recursiveGen = _out235;
            _1593_recOwned = _out236;
            _1594_recIdents = _out237;
            RAST._IExpr _out238;
            DCOMP._IOwnership _out239;
            DCOMP.COMP.FromOwnership(RAST.Expr.create_TypeAscription((_1592_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1575_nativeToType).dtor_value), _1593_recOwned, expectedOwnership, out _out238, out _out239);
            r = _out238;
            resultingOwnership = _out239;
            readIdents = _1594_recIdents;
            return ;
          }
        }
        RAST._IExpr _out240;
        DCOMP._IOwnership _out241;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out242;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1566_expr, _1567_fromTpe, _1571_b), _1571_b, _1568_toTpe), selfIdent, env, expectedOwnership, out _out240, out _out241, out _out242);
        r = _out240;
        resultingOwnership = _out241;
        readIdents = _out242;
      }
    }
    public void GenExprConvertFromNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs58 = e;
      DAST._IExpression _1595_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _1596_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _1597_toTpe = _let_tmp_rhs58.dtor_typ;
      DAST._IType _let_tmp_rhs59 = _1596_fromTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1598___v100 = _let_tmp_rhs59.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _1599___v101 = _let_tmp_rhs59.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs60 = _let_tmp_rhs59.dtor_resolved;
      DAST._IType _1600_b = _let_tmp_rhs60.dtor_baseType;
      DAST._INewtypeRange _1601_range = _let_tmp_rhs60.dtor_range;
      bool _1602_erase = _let_tmp_rhs60.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1603_attributes = _let_tmp_rhs60.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _1604_nativeFromType;
      _1604_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1600_b, _1601_range);
      if (object.Equals(_1600_b, _1597_toTpe)) {
        RAST._IExpr _1605_recursiveGen;
        DCOMP._IOwnership _1606_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1607_recIdents;
        RAST._IExpr _out243;
        DCOMP._IOwnership _out244;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out245;
        (this).GenExpr(_1595_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out243, out _out244, out _out245);
        _1605_recursiveGen = _out243;
        _1606_recOwned = _out244;
        _1607_recIdents = _out245;
        readIdents = _1607_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source81 = _1604_nativeFromType;
        bool unmatched81 = true;
        if (unmatched81) {
          if (_source81.is_Some) {
            RAST._IType _1608_v = _source81.dtor_value;
            unmatched81 = false;
            RAST._IType _1609_toTpeRust;
            RAST._IType _out246;
            _out246 = (this).GenType(_1597_toTpe, false, false);
            _1609_toTpeRust = _out246;
            r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1609_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1605_recursiveGen));
            RAST._IExpr _out247;
            DCOMP._IOwnership _out248;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out247, out _out248);
            r = _out247;
            resultingOwnership = _out248;
          }
        }
        if (unmatched81) {
          unmatched81 = false;
          if (_1602_erase) {
            r = _1605_recursiveGen;
          } else {
            r = (_1605_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out249;
          DCOMP._IOwnership _out250;
          DCOMP.COMP.FromOwnership(r, _1606_recOwned, expectedOwnership, out _out249, out _out250);
          r = _out249;
          resultingOwnership = _out250;
        }
      } else {
        if ((_1604_nativeFromType).is_Some) {
          if (object.Equals(_1597_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1610_recursiveGen;
            DCOMP._IOwnership _1611_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1612_recIdents;
            RAST._IExpr _out251;
            DCOMP._IOwnership _out252;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out253;
            (this).GenExpr(_1595_expr, selfIdent, env, expectedOwnership, out _out251, out _out252, out _out253);
            _1610_recursiveGen = _out251;
            _1611_recOwned = _out252;
            _1612_recIdents = _out253;
            RAST._IExpr _out254;
            DCOMP._IOwnership _out255;
            DCOMP.COMP.FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1610_recursiveGen, (this).DafnyCharUnderlying)), _1611_recOwned, expectedOwnership, out _out254, out _out255);
            r = _out254;
            resultingOwnership = _out255;
            readIdents = _1612_recIdents;
            return ;
          }
        }
        RAST._IExpr _out256;
        DCOMP._IOwnership _out257;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out258;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1595_expr, _1596_fromTpe, _1600_b), _1600_b, _1597_toTpe), selfIdent, env, expectedOwnership, out _out256, out _out257, out _out258);
        r = _out256;
        resultingOwnership = _out257;
        readIdents = _out258;
      }
    }
    public void GenExprConvertNotImplemented(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs61 = e;
      DAST._IExpression _1613_expr = _let_tmp_rhs61.dtor_value;
      DAST._IType _1614_fromTpe = _let_tmp_rhs61.dtor_from;
      DAST._IType _1615_toTpe = _let_tmp_rhs61.dtor_typ;
      RAST._IType _1616_fromTpeGen;
      RAST._IType _out259;
      _out259 = (this).GenType(_1614_fromTpe, true, false);
      _1616_fromTpeGen = _out259;
      RAST._IType _1617_toTpeGen;
      RAST._IType _out260;
      _out260 = (this).GenType(_1615_toTpe, true, false);
      _1617_toTpeGen = _out260;
      RAST._IExpr _1618_recursiveGen;
      DCOMP._IOwnership _1619_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1620_recIdents;
      RAST._IExpr _out261;
      DCOMP._IOwnership _out262;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out263;
      (this).GenExpr(_1613_expr, selfIdent, env, expectedOwnership, out _out261, out _out262, out _out263);
      _1618_recursiveGen = _out261;
      _1619_recOwned = _out262;
      _1620_recIdents = _out263;
      readIdents = _1620_recIdents;
      if (RAST.__default.IsImmutableConversion(_1616_fromTpeGen, _1617_toTpeGen)) {
        RAST._IExpr _out264;
        DCOMP._IOwnership _out265;
        DCOMP.COMP.FromOwnership(_1618_recursiveGen, _1619_recOwned, DCOMP.Ownership.create_OwnershipOwned(), out _out264, out _out265);
        r = _out264;
        resultingOwnership = _out265;
        r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("UpcastTo"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1617_toTpeGen))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast_to"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1618_recursiveGen));
        RAST._IExpr _out266;
        DCOMP._IOwnership _out267;
        DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out266, out _out267);
        r = _out266;
        resultingOwnership = _out267;
      } else {
        Dafny.ISequence<Dafny.Rune> _1621_msg;
        _1621_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1616_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1617_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1621_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1618_recursiveGen)._ToString(DCOMP.__default.IND), _1621_msg));
        RAST._IExpr _out268;
        DCOMP._IOwnership _out269;
        DCOMP.COMP.FromOwnership(r, _1619_recOwned, expectedOwnership, out _out268, out _out269);
        r = _out268;
        resultingOwnership = _out269;
      }
    }
    public void GenExprConvert(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs62 = e;
      DAST._IExpression _1622_expr = _let_tmp_rhs62.dtor_value;
      DAST._IType _1623_fromTpe = _let_tmp_rhs62.dtor_from;
      DAST._IType _1624_toTpe = _let_tmp_rhs62.dtor_typ;
      if (object.Equals(_1623_fromTpe, _1624_toTpe)) {
        RAST._IExpr _1625_recursiveGen;
        DCOMP._IOwnership _1626_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1627_recIdents;
        RAST._IExpr _out270;
        DCOMP._IOwnership _out271;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out272;
        (this).GenExpr(_1622_expr, selfIdent, env, expectedOwnership, out _out270, out _out271, out _out272);
        _1625_recursiveGen = _out270;
        _1626_recOwned = _out271;
        _1627_recIdents = _out272;
        r = _1625_recursiveGen;
        RAST._IExpr _out273;
        DCOMP._IOwnership _out274;
        DCOMP.COMP.FromOwnership(r, _1626_recOwned, expectedOwnership, out _out273, out _out274);
        r = _out273;
        resultingOwnership = _out274;
        readIdents = _1627_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source82 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1623_fromTpe, _1624_toTpe);
        bool unmatched82 = true;
        if (unmatched82) {
          DAST._IType _01 = _source82.dtor__0;
          if (_01.is_Nullable) {
            DAST._IType _1628___v102 = _01.dtor_Nullable_a0;
            DAST._IType _1629___v103 = _source82.dtor__1;
            unmatched82 = false;
            {
              RAST._IExpr _out275;
              DCOMP._IOwnership _out276;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out277;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out275, out _out276, out _out277);
              r = _out275;
              resultingOwnership = _out276;
              readIdents = _out277;
            }
          }
        }
        if (unmatched82) {
          DAST._IType _1630___v104 = _source82.dtor__0;
          DAST._IType _11 = _source82.dtor__1;
          if (_11.is_Nullable) {
            DAST._IType _1631___v105 = _11.dtor_Nullable_a0;
            unmatched82 = false;
            {
              RAST._IExpr _out278;
              DCOMP._IOwnership _out279;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out280;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out278, out _out279, out _out280);
              r = _out278;
              resultingOwnership = _out279;
              readIdents = _out280;
            }
          }
        }
        if (unmatched82) {
          DAST._IType _1632___v106 = _source82.dtor__0;
          DAST._IType _12 = _source82.dtor__1;
          if (_12.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1633___v107 = _12.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1634___v108 = _12.dtor_typeArgs;
            DAST._IResolvedType resolved2 = _12.dtor_resolved;
            if (resolved2.is_Newtype) {
              DAST._IType _1635_b = resolved2.dtor_baseType;
              DAST._INewtypeRange _1636_range = resolved2.dtor_range;
              bool _1637_erase = resolved2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1638_attributes = resolved2.dtor_attributes;
              unmatched82 = false;
              {
                RAST._IExpr _out281;
                DCOMP._IOwnership _out282;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out283;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out281, out _out282, out _out283);
                r = _out281;
                resultingOwnership = _out282;
                readIdents = _out283;
              }
            }
          }
        }
        if (unmatched82) {
          DAST._IType _02 = _source82.dtor__0;
          if (_02.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1639___v109 = _02.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1640___v110 = _02.dtor_typeArgs;
            DAST._IResolvedType resolved3 = _02.dtor_resolved;
            if (resolved3.is_Newtype) {
              DAST._IType _1641_b = resolved3.dtor_baseType;
              DAST._INewtypeRange _1642_range = resolved3.dtor_range;
              bool _1643_erase = resolved3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1644_attributes = resolved3.dtor_attributes;
              DAST._IType _1645___v111 = _source82.dtor__1;
              unmatched82 = false;
              {
                RAST._IExpr _out284;
                DCOMP._IOwnership _out285;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out286;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out284, out _out285, out _out286);
                r = _out284;
                resultingOwnership = _out285;
                readIdents = _out286;
              }
            }
          }
        }
        if (unmatched82) {
          DAST._IType _03 = _source82.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h92 = _03.dtor_Primitive_a0;
            if (_h92.is_Int) {
              DAST._IType _13 = _source82.dtor__1;
              if (_13.is_Primitive) {
                DAST._IPrimitive _h93 = _13.dtor_Primitive_a0;
                if (_h93.is_Real) {
                  unmatched82 = false;
                  {
                    RAST._IExpr _1646_recursiveGen;
                    DCOMP._IOwnership _1647___v112;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1648_recIdents;
                    RAST._IExpr _out287;
                    DCOMP._IOwnership _out288;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out289;
                    (this).GenExpr(_1622_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out287, out _out288, out _out289);
                    _1646_recursiveGen = _out287;
                    _1647___v112 = _out288;
                    _1648_recIdents = _out289;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1646_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out290;
                    DCOMP._IOwnership _out291;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out290, out _out291);
                    r = _out290;
                    resultingOwnership = _out291;
                    readIdents = _1648_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched82) {
          DAST._IType _04 = _source82.dtor__0;
          if (_04.is_Primitive) {
            DAST._IPrimitive _h94 = _04.dtor_Primitive_a0;
            if (_h94.is_Real) {
              DAST._IType _14 = _source82.dtor__1;
              if (_14.is_Primitive) {
                DAST._IPrimitive _h95 = _14.dtor_Primitive_a0;
                if (_h95.is_Int) {
                  unmatched82 = false;
                  {
                    RAST._IExpr _1649_recursiveGen;
                    DCOMP._IOwnership _1650___v113;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1651_recIdents;
                    RAST._IExpr _out292;
                    DCOMP._IOwnership _out293;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out294;
                    (this).GenExpr(_1622_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out292, out _out293, out _out294);
                    _1649_recursiveGen = _out292;
                    _1650___v113 = _out293;
                    _1651_recIdents = _out294;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1649_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out295;
                    DCOMP._IOwnership _out296;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out295, out _out296);
                    r = _out295;
                    resultingOwnership = _out296;
                    readIdents = _1651_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched82) {
          DAST._IType _05 = _source82.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h96 = _05.dtor_Primitive_a0;
            if (_h96.is_Int) {
              DAST._IType _15 = _source82.dtor__1;
              if (_15.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1652___v114 = _15.dtor_Passthrough_a0;
                unmatched82 = false;
                {
                  RAST._IType _1653_rhsType;
                  RAST._IType _out297;
                  _out297 = (this).GenType(_1624_toTpe, true, false);
                  _1653_rhsType = _out297;
                  RAST._IExpr _1654_recursiveGen;
                  DCOMP._IOwnership _1655___v115;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1656_recIdents;
                  RAST._IExpr _out298;
                  DCOMP._IOwnership _out299;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out300;
                  (this).GenExpr(_1622_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out298, out _out299, out _out300);
                  _1654_recursiveGen = _out298;
                  _1655___v115 = _out299;
                  _1656_recIdents = _out300;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1653_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1654_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out301;
                  DCOMP._IOwnership _out302;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out301, out _out302);
                  r = _out301;
                  resultingOwnership = _out302;
                  readIdents = _1656_recIdents;
                }
              }
            }
          }
        }
        if (unmatched82) {
          DAST._IType _06 = _source82.dtor__0;
          if (_06.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1657___v116 = _06.dtor_Passthrough_a0;
            DAST._IType _16 = _source82.dtor__1;
            if (_16.is_Primitive) {
              DAST._IPrimitive _h97 = _16.dtor_Primitive_a0;
              if (_h97.is_Int) {
                unmatched82 = false;
                {
                  RAST._IType _1658_rhsType;
                  RAST._IType _out303;
                  _out303 = (this).GenType(_1623_fromTpe, true, false);
                  _1658_rhsType = _out303;
                  RAST._IExpr _1659_recursiveGen;
                  DCOMP._IOwnership _1660___v117;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1661_recIdents;
                  RAST._IExpr _out304;
                  DCOMP._IOwnership _out305;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out306;
                  (this).GenExpr(_1622_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out304, out _out305, out _out306);
                  _1659_recursiveGen = _out304;
                  _1660___v117 = _out305;
                  _1661_recIdents = _out306;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::dafny_runtime::BigInt::from("), (_1659_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")}")));
                  RAST._IExpr _out307;
                  DCOMP._IOwnership _out308;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out307, out _out308);
                  r = _out307;
                  resultingOwnership = _out308;
                  readIdents = _1661_recIdents;
                }
              }
            }
          }
        }
        if (unmatched82) {
          DAST._IType _07 = _source82.dtor__0;
          if (_07.is_Primitive) {
            DAST._IPrimitive _h98 = _07.dtor_Primitive_a0;
            if (_h98.is_Int) {
              DAST._IType _17 = _source82.dtor__1;
              if (_17.is_Primitive) {
                DAST._IPrimitive _h99 = _17.dtor_Primitive_a0;
                if (_h99.is_Char) {
                  unmatched82 = false;
                  {
                    RAST._IType _1662_rhsType;
                    RAST._IType _out309;
                    _out309 = (this).GenType(_1624_toTpe, true, false);
                    _1662_rhsType = _out309;
                    RAST._IExpr _1663_recursiveGen;
                    DCOMP._IOwnership _1664___v118;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1665_recIdents;
                    RAST._IExpr _out310;
                    DCOMP._IOwnership _out311;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out312;
                    (this).GenExpr(_1622_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out310, out _out311, out _out312);
                    _1663_recursiveGen = _out310;
                    _1664___v118 = _out311;
                    _1665_recIdents = _out312;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), (_1663_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()")));
                    RAST._IExpr _out313;
                    DCOMP._IOwnership _out314;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out313, out _out314);
                    r = _out313;
                    resultingOwnership = _out314;
                    readIdents = _1665_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched82) {
          DAST._IType _08 = _source82.dtor__0;
          if (_08.is_Primitive) {
            DAST._IPrimitive _h910 = _08.dtor_Primitive_a0;
            if (_h910.is_Char) {
              DAST._IType _18 = _source82.dtor__1;
              if (_18.is_Primitive) {
                DAST._IPrimitive _h911 = _18.dtor_Primitive_a0;
                if (_h911.is_Int) {
                  unmatched82 = false;
                  {
                    RAST._IType _1666_rhsType;
                    RAST._IType _out315;
                    _out315 = (this).GenType(_1623_fromTpe, true, false);
                    _1666_rhsType = _out315;
                    RAST._IExpr _1667_recursiveGen;
                    DCOMP._IOwnership _1668___v119;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1669_recIdents;
                    RAST._IExpr _out316;
                    DCOMP._IOwnership _out317;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out318;
                    (this).GenExpr(_1622_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out316, out _out317, out _out318);
                    _1667_recursiveGen = _out316;
                    _1668___v119 = _out317;
                    _1669_recIdents = _out318;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1667_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out319;
                    DCOMP._IOwnership _out320;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out319, out _out320);
                    r = _out319;
                    resultingOwnership = _out320;
                    readIdents = _1669_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched82) {
          DAST._IType _09 = _source82.dtor__0;
          if (_09.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1670___v120 = _09.dtor_Passthrough_a0;
            DAST._IType _19 = _source82.dtor__1;
            if (_19.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1671___v121 = _19.dtor_Passthrough_a0;
              unmatched82 = false;
              {
                RAST._IExpr _1672_recursiveGen;
                DCOMP._IOwnership _1673___v122;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1674_recIdents;
                RAST._IExpr _out321;
                DCOMP._IOwnership _out322;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out323;
                (this).GenExpr(_1622_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out321, out _out322, out _out323);
                _1672_recursiveGen = _out321;
                _1673___v122 = _out322;
                _1674_recIdents = _out323;
                RAST._IType _1675_toTpeGen;
                RAST._IType _out324;
                _out324 = (this).GenType(_1624_toTpe, true, false);
                _1675_toTpeGen = _out324;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1672_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1675_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out325;
                DCOMP._IOwnership _out326;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out325, out _out326);
                r = _out325;
                resultingOwnership = _out326;
                readIdents = _1674_recIdents;
              }
            }
          }
        }
        if (unmatched82) {
          _System._ITuple2<DAST._IType, DAST._IType> _1676___v123 = _source82;
          unmatched82 = false;
          {
            RAST._IExpr _out327;
            DCOMP._IOwnership _out328;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out329;
            (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out327, out _out328, out _out329);
            r = _out327;
            resultingOwnership = _out328;
            readIdents = _out329;
          }
        }
      }
      return ;
    }
    public void GenIdent(Dafny.ISequence<Dafny.Rune> rName, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      r = RAST.Expr.create_Identifier(rName);
      Std.Wrappers._IOption<RAST._IType> _1677_tpe;
      _1677_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1678_placeboOpt;
      _1678_placeboOpt = (((_1677_tpe).is_Some) ? (((_1677_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _1679_currentlyBorrowed;
      _1679_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1680_noNeedOfClone;
      _1680_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1678_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _1679_currentlyBorrowed = false;
        _1680_noNeedOfClone = true;
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if (((_1677_tpe).is_Some) && (((_1677_tpe).dtor_value).IsObjectOrPointer())) {
          r = ((this).modify__macro).Apply1(r);
        } else {
          r = RAST.__default.BorrowMut(r);
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        if (!(_1680_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1680_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1679_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (((_1677_tpe).is_Some) && (((_1677_tpe).dtor_value).IsPointer())) {
          r = ((this).read__macro).Apply1(r);
        } else {
          r = RAST.__default.Borrow(r);
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      }
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(rName);
      return ;
    }
    public void GenExpr(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source83 = e;
      bool unmatched83 = true;
      if (unmatched83) {
        if (_source83.is_Literal) {
          DAST._ILiteral _1681___v124 = _source83.dtor_Literal_a0;
          unmatched83 = false;
          RAST._IExpr _out330;
          DCOMP._IOwnership _out331;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out332;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out330, out _out331, out _out332);
          r = _out330;
          resultingOwnership = _out331;
          readIdents = _out332;
        }
      }
      if (unmatched83) {
        if (_source83.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1682_name = _source83.dtor_Ident_a0;
          unmatched83 = false;
          {
            RAST._IExpr _out333;
            DCOMP._IOwnership _out334;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out335;
            (this).GenIdent(DCOMP.__default.escapeName(_1682_name), selfIdent, env, expectedOwnership, out _out333, out _out334, out _out335);
            r = _out333;
            resultingOwnership = _out334;
            readIdents = _out335;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1683_path = _source83.dtor_Companion_a0;
          unmatched83 = false;
          {
            RAST._IExpr _out336;
            _out336 = DCOMP.COMP.GenPathExpr(_1683_path);
            r = _out336;
            if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else {
              RAST._IExpr _out337;
              DCOMP._IOwnership _out338;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out337, out _out338);
              r = _out337;
              resultingOwnership = _out338;
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_InitializationValue) {
          DAST._IType _1684_typ = _source83.dtor_typ;
          unmatched83 = false;
          {
            RAST._IType _1685_typExpr;
            RAST._IType _out339;
            _out339 = (this).GenType(_1684_typ, false, false);
            _1685_typExpr = _out339;
            if ((_1685_typExpr).IsObjectOrPointer()) {
              r = (_1685_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1685_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
            }
            RAST._IExpr _out340;
            DCOMP._IOwnership _out341;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out340, out _out341);
            r = _out340;
            resultingOwnership = _out341;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _1686_values = _source83.dtor_Tuple_a0;
          unmatched83 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1687_exprs;
            _1687_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi33 = new BigInteger((_1686_values).Count);
            for (BigInteger _1688_i = BigInteger.Zero; _1688_i < _hi33; _1688_i++) {
              RAST._IExpr _1689_recursiveGen;
              DCOMP._IOwnership _1690___v125;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1691_recIdents;
              RAST._IExpr _out342;
              DCOMP._IOwnership _out343;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out344;
              (this).GenExpr((_1686_values).Select(_1688_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out342, out _out343, out _out344);
              _1689_recursiveGen = _out342;
              _1690___v125 = _out343;
              _1691_recIdents = _out344;
              _1687_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1687_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1689_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1691_recIdents);
            }
            r = (((new BigInteger((_1686_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_1687_exprs)) : (RAST.__default.SystemTuple(_1687_exprs)));
            RAST._IExpr _out345;
            DCOMP._IOwnership _out346;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out345, out _out346);
            r = _out345;
            resultingOwnership = _out346;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1692_path = _source83.dtor_path;
          Dafny.ISequence<DAST._IType> _1693_typeArgs = _source83.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1694_args = _source83.dtor_args;
          unmatched83 = false;
          {
            RAST._IExpr _out347;
            _out347 = DCOMP.COMP.GenPathExpr(_1692_path);
            r = _out347;
            if ((new BigInteger((_1693_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1695_typeExprs;
              _1695_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi34 = new BigInteger((_1693_typeArgs).Count);
              for (BigInteger _1696_i = BigInteger.Zero; _1696_i < _hi34; _1696_i++) {
                RAST._IType _1697_typeExpr;
                RAST._IType _out348;
                _out348 = (this).GenType((_1693_typeArgs).Select(_1696_i), false, false);
                _1697_typeExpr = _out348;
                _1695_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1695_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1697_typeExpr));
              }
              r = (r).ApplyType(_1695_typeExprs);
            }
            r = (r).MSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1698_arguments;
            _1698_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi35 = new BigInteger((_1694_args).Count);
            for (BigInteger _1699_i = BigInteger.Zero; _1699_i < _hi35; _1699_i++) {
              RAST._IExpr _1700_recursiveGen;
              DCOMP._IOwnership _1701___v126;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1702_recIdents;
              RAST._IExpr _out349;
              DCOMP._IOwnership _out350;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out351;
              (this).GenExpr((_1694_args).Select(_1699_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out349, out _out350, out _out351);
              _1700_recursiveGen = _out349;
              _1701___v126 = _out350;
              _1702_recIdents = _out351;
              _1698_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1698_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1700_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1702_recIdents);
            }
            r = (r).Apply(_1698_arguments);
            RAST._IExpr _out352;
            DCOMP._IOwnership _out353;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out352, out _out353);
            r = _out352;
            resultingOwnership = _out353;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_NewUninitArray) {
          Dafny.ISequence<DAST._IExpression> _1703_dims = _source83.dtor_dims;
          DAST._IType _1704_typ = _source83.dtor_typ;
          unmatched83 = false;
          {
            if ((new BigInteger(16)) < (new BigInteger((_1703_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _1705_msg;
              _1705_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1705_msg);
              }
              r = RAST.Expr.create_RawExpr(_1705_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _1706_typeGen;
              RAST._IType _out354;
              _out354 = (this).GenType(_1704_typ, false, false);
              _1706_typeGen = _out354;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _1707_dimExprs;
              _1707_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi36 = new BigInteger((_1703_dims).Count);
              for (BigInteger _1708_i = BigInteger.Zero; _1708_i < _hi36; _1708_i++) {
                RAST._IExpr _1709_recursiveGen;
                DCOMP._IOwnership _1710___v127;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1711_recIdents;
                RAST._IExpr _out355;
                DCOMP._IOwnership _out356;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out357;
                (this).GenExpr((_1703_dims).Select(_1708_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out355, out _out356, out _out357);
                _1709_recursiveGen = _out355;
                _1710___v127 = _out356;
                _1711_recIdents = _out357;
                _1707_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1707_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(((_1709_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_usize"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1711_recIdents);
              }
              if ((new BigInteger((_1703_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _1712_class__name;
                _1712_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_1703_dims).Count)));
                r = ((((RAST.__default.dafny__runtime).MSel(_1712_class__name)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1706_typeGen))).MSel((this).placebos__usize)).Apply(_1707_dimExprs);
              } else {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1706_typeGen))).Apply(_1707_dimExprs);
              }
            }
            RAST._IExpr _out358;
            DCOMP._IOwnership _out359;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out358, out _out359);
            r = _out358;
            resultingOwnership = _out359;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_ArrayIndexToInt) {
          DAST._IExpression _1713_underlying = _source83.dtor_value;
          unmatched83 = false;
          {
            RAST._IExpr _1714_recursiveGen;
            DCOMP._IOwnership _1715___v128;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1716_recIdents;
            RAST._IExpr _out360;
            DCOMP._IOwnership _out361;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out362;
            (this).GenExpr(_1713_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out360, out _out361, out _out362);
            _1714_recursiveGen = _out360;
            _1715___v128 = _out361;
            _1716_recIdents = _out362;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(_1714_recursiveGen);
            readIdents = _1716_recIdents;
            RAST._IExpr _out363;
            DCOMP._IOwnership _out364;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out363, out _out364);
            r = _out363;
            resultingOwnership = _out364;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_FinalizeNewArray) {
          DAST._IExpression _1717_underlying = _source83.dtor_value;
          DAST._IType _1718_typ = _source83.dtor_typ;
          unmatched83 = false;
          {
            RAST._IType _1719_tpe;
            RAST._IType _out365;
            _out365 = (this).GenType(_1718_typ, false, false);
            _1719_tpe = _out365;
            RAST._IExpr _1720_recursiveGen;
            DCOMP._IOwnership _1721___v129;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1722_recIdents;
            RAST._IExpr _out366;
            DCOMP._IOwnership _out367;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out368;
            (this).GenExpr(_1717_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out366, out _out367, out _out368);
            _1720_recursiveGen = _out366;
            _1721___v129 = _out367;
            _1722_recIdents = _out368;
            readIdents = _1722_recIdents;
            if ((_1719_tpe).IsObjectOrPointer()) {
              RAST._IType _1723_t;
              _1723_t = (_1719_tpe).ObjectOrPointerUnderlying();
              if ((_1723_t).is_Array) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).array__construct)).Apply1(_1720_recursiveGen);
              } else if ((_1723_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _1724_c;
                _1724_c = (_1723_t).MultiArrayClass();
                r = (((RAST.__default.dafny__runtime).MSel(_1724_c)).MSel((this).array__construct)).Apply1(_1720_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_1719_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_1719_tpe)._ToString(DCOMP.__default.IND)));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            }
            RAST._IExpr _out369;
            DCOMP._IOwnership _out370;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out369, out _out370);
            r = _out369;
            resultingOwnership = _out370;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_DatatypeValue) {
          DAST._IDatatypeType _1725_datatypeType = _source83.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1726_typeArgs = _source83.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1727_variant = _source83.dtor_variant;
          bool _1728_isCo = _source83.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1729_values = _source83.dtor_contents;
          unmatched83 = false;
          {
            RAST._IExpr _out371;
            _out371 = DCOMP.COMP.GenPathExpr((_1725_datatypeType).dtor_path);
            r = _out371;
            Dafny.ISequence<RAST._IType> _1730_genTypeArgs;
            _1730_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi37 = new BigInteger((_1726_typeArgs).Count);
            for (BigInteger _1731_i = BigInteger.Zero; _1731_i < _hi37; _1731_i++) {
              RAST._IType _1732_typeExpr;
              RAST._IType _out372;
              _out372 = (this).GenType((_1726_typeArgs).Select(_1731_i), false, false);
              _1732_typeExpr = _out372;
              _1730_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1730_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1732_typeExpr));
            }
            if ((new BigInteger((_1726_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1730_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1727_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1733_assignments;
            _1733_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi38 = new BigInteger((_1729_values).Count);
            for (BigInteger _1734_i = BigInteger.Zero; _1734_i < _hi38; _1734_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs63 = (_1729_values).Select(_1734_i);
              Dafny.ISequence<Dafny.Rune> _1735_name = _let_tmp_rhs63.dtor__0;
              DAST._IExpression _1736_value = _let_tmp_rhs63.dtor__1;
              if (_1728_isCo) {
                RAST._IExpr _1737_recursiveGen;
                DCOMP._IOwnership _1738___v130;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1739_recIdents;
                RAST._IExpr _out373;
                DCOMP._IOwnership _out374;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out375;
                (this).GenExpr(_1736_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out373, out _out374, out _out375);
                _1737_recursiveGen = _out373;
                _1738___v130 = _out374;
                _1739_recIdents = _out375;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1739_recIdents);
                Dafny.ISequence<Dafny.Rune> _1740_allReadCloned;
                _1740_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1739_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1741_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1739_recIdents).Elements) {
                    _1741_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1739_recIdents).Contains(_1741_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 3743)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1740_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1740_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1741_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1741_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1739_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1739_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1741_next));
                }
                Dafny.ISequence<Dafny.Rune> _1742_wasAssigned;
                _1742_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1740_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1737_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1733_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1733_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1735_name, RAST.Expr.create_RawExpr(_1742_wasAssigned))));
              } else {
                RAST._IExpr _1743_recursiveGen;
                DCOMP._IOwnership _1744___v131;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1745_recIdents;
                RAST._IExpr _out376;
                DCOMP._IOwnership _out377;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out378;
                (this).GenExpr(_1736_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out376, out _out377, out _out378);
                _1743_recursiveGen = _out376;
                _1744___v131 = _out377;
                _1745_recIdents = _out378;
                _1733_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1733_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1735_name, _1743_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1745_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1733_assignments);
            if ((this).IsRcWrapped((_1725_datatypeType).dtor_attributes)) {
              r = RAST.__default.RcNew(r);
            }
            RAST._IExpr _out379;
            DCOMP._IOwnership _out380;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out379, out _out380);
            r = _out379;
            resultingOwnership = _out380;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_Convert) {
          DAST._IExpression _1746___v132 = _source83.dtor_value;
          DAST._IType _1747___v133 = _source83.dtor_from;
          DAST._IType _1748___v134 = _source83.dtor_typ;
          unmatched83 = false;
          {
            RAST._IExpr _out381;
            DCOMP._IOwnership _out382;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out383;
            (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out381, out _out382, out _out383);
            r = _out381;
            resultingOwnership = _out382;
            readIdents = _out383;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_SeqConstruct) {
          DAST._IExpression _1749_length = _source83.dtor_length;
          DAST._IExpression _1750_expr = _source83.dtor_elem;
          unmatched83 = false;
          {
            RAST._IExpr _1751_recursiveGen;
            DCOMP._IOwnership _1752___v135;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1753_recIdents;
            RAST._IExpr _out384;
            DCOMP._IOwnership _out385;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out386;
            (this).GenExpr(_1750_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out384, out _out385, out _out386);
            _1751_recursiveGen = _out384;
            _1752___v135 = _out385;
            _1753_recIdents = _out386;
            RAST._IExpr _1754_lengthGen;
            DCOMP._IOwnership _1755___v136;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1756_lengthIdents;
            RAST._IExpr _out387;
            DCOMP._IOwnership _out388;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out389;
            (this).GenExpr(_1749_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out387, out _out388, out _out389);
            _1754_lengthGen = _out387;
            _1755___v136 = _out388;
            _1756_lengthIdents = _out389;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1751_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1754_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1753_recIdents, _1756_lengthIdents);
            RAST._IExpr _out390;
            DCOMP._IOwnership _out391;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out390, out _out391);
            r = _out390;
            resultingOwnership = _out391;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _1757_exprs = _source83.dtor_elements;
          DAST._IType _1758_typ = _source83.dtor_typ;
          unmatched83 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1759_genTpe;
            RAST._IType _out392;
            _out392 = (this).GenType(_1758_typ, false, false);
            _1759_genTpe = _out392;
            BigInteger _1760_i;
            _1760_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1761_args;
            _1761_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1760_i) < (new BigInteger((_1757_exprs).Count))) {
              RAST._IExpr _1762_recursiveGen;
              DCOMP._IOwnership _1763___v137;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1764_recIdents;
              RAST._IExpr _out393;
              DCOMP._IOwnership _out394;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out395;
              (this).GenExpr((_1757_exprs).Select(_1760_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out393, out _out394, out _out395);
              _1762_recursiveGen = _out393;
              _1763___v137 = _out394;
              _1764_recIdents = _out395;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1764_recIdents);
              _1761_args = Dafny.Sequence<RAST._IExpr>.Concat(_1761_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1762_recursiveGen));
              _1760_i = (_1760_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_1761_args);
            if ((new BigInteger((_1761_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1759_genTpe));
            }
            RAST._IExpr _out396;
            DCOMP._IOwnership _out397;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out396, out _out397);
            r = _out396;
            resultingOwnership = _out397;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _1765_exprs = _source83.dtor_elements;
          unmatched83 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1766_generatedValues;
            _1766_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1767_i;
            _1767_i = BigInteger.Zero;
            while ((_1767_i) < (new BigInteger((_1765_exprs).Count))) {
              RAST._IExpr _1768_recursiveGen;
              DCOMP._IOwnership _1769___v138;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1770_recIdents;
              RAST._IExpr _out398;
              DCOMP._IOwnership _out399;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out400;
              (this).GenExpr((_1765_exprs).Select(_1767_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out398, out _out399, out _out400);
              _1768_recursiveGen = _out398;
              _1769___v138 = _out399;
              _1770_recIdents = _out400;
              _1766_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1766_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1768_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1770_recIdents);
              _1767_i = (_1767_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_1766_generatedValues);
            RAST._IExpr _out401;
            DCOMP._IOwnership _out402;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out401, out _out402);
            r = _out401;
            resultingOwnership = _out402;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _1771_exprs = _source83.dtor_elements;
          unmatched83 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1772_generatedValues;
            _1772_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1773_i;
            _1773_i = BigInteger.Zero;
            while ((_1773_i) < (new BigInteger((_1771_exprs).Count))) {
              RAST._IExpr _1774_recursiveGen;
              DCOMP._IOwnership _1775___v139;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1776_recIdents;
              RAST._IExpr _out403;
              DCOMP._IOwnership _out404;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out405;
              (this).GenExpr((_1771_exprs).Select(_1773_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out403, out _out404, out _out405);
              _1774_recursiveGen = _out403;
              _1775___v139 = _out404;
              _1776_recIdents = _out405;
              _1772_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1772_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1774_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1776_recIdents);
              _1773_i = (_1773_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_1772_generatedValues);
            RAST._IExpr _out406;
            DCOMP._IOwnership _out407;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out406, out _out407);
            r = _out406;
            resultingOwnership = _out407;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_ToMultiset) {
          DAST._IExpression _1777_expr = _source83.dtor_ToMultiset_a0;
          unmatched83 = false;
          {
            RAST._IExpr _1778_recursiveGen;
            DCOMP._IOwnership _1779___v140;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1780_recIdents;
            RAST._IExpr _out408;
            DCOMP._IOwnership _out409;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out410;
            (this).GenExpr(_1777_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out408, out _out409, out _out410);
            _1778_recursiveGen = _out408;
            _1779___v140 = _out409;
            _1780_recIdents = _out410;
            r = ((_1778_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _1780_recIdents;
            RAST._IExpr _out411;
            DCOMP._IOwnership _out412;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out411, out _out412);
            r = _out411;
            resultingOwnership = _out412;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1781_mapElems = _source83.dtor_mapElems;
          unmatched83 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1782_generatedValues;
            _1782_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1783_i;
            _1783_i = BigInteger.Zero;
            while ((_1783_i) < (new BigInteger((_1781_mapElems).Count))) {
              RAST._IExpr _1784_recursiveGenKey;
              DCOMP._IOwnership _1785___v141;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1786_recIdentsKey;
              RAST._IExpr _out413;
              DCOMP._IOwnership _out414;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out415;
              (this).GenExpr(((_1781_mapElems).Select(_1783_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out413, out _out414, out _out415);
              _1784_recursiveGenKey = _out413;
              _1785___v141 = _out414;
              _1786_recIdentsKey = _out415;
              RAST._IExpr _1787_recursiveGenValue;
              DCOMP._IOwnership _1788___v142;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1789_recIdentsValue;
              RAST._IExpr _out416;
              DCOMP._IOwnership _out417;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out418;
              (this).GenExpr(((_1781_mapElems).Select(_1783_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out416, out _out417, out _out418);
              _1787_recursiveGenValue = _out416;
              _1788___v142 = _out417;
              _1789_recIdentsValue = _out418;
              _1782_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1782_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1784_recursiveGenKey, _1787_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1786_recIdentsKey), _1789_recIdentsValue);
              _1783_i = (_1783_i) + (BigInteger.One);
            }
            _1783_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1790_arguments;
            _1790_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1783_i) < (new BigInteger((_1782_generatedValues).Count))) {
              RAST._IExpr _1791_genKey;
              _1791_genKey = ((_1782_generatedValues).Select(_1783_i)).dtor__0;
              RAST._IExpr _1792_genValue;
              _1792_genValue = ((_1782_generatedValues).Select(_1783_i)).dtor__1;
              _1790_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1790_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1791_genKey, _1792_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _1783_i = (_1783_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_1790_arguments);
            RAST._IExpr _out419;
            DCOMP._IOwnership _out420;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out419, out _out420);
            r = _out419;
            resultingOwnership = _out420;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_SeqUpdate) {
          DAST._IExpression _1793_expr = _source83.dtor_expr;
          DAST._IExpression _1794_index = _source83.dtor_indexExpr;
          DAST._IExpression _1795_value = _source83.dtor_value;
          unmatched83 = false;
          {
            RAST._IExpr _1796_exprR;
            DCOMP._IOwnership _1797___v143;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1798_exprIdents;
            RAST._IExpr _out421;
            DCOMP._IOwnership _out422;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out423;
            (this).GenExpr(_1793_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out421, out _out422, out _out423);
            _1796_exprR = _out421;
            _1797___v143 = _out422;
            _1798_exprIdents = _out423;
            RAST._IExpr _1799_indexR;
            DCOMP._IOwnership _1800_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1801_indexIdents;
            RAST._IExpr _out424;
            DCOMP._IOwnership _out425;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out426;
            (this).GenExpr(_1794_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out424, out _out425, out _out426);
            _1799_indexR = _out424;
            _1800_indexOwnership = _out425;
            _1801_indexIdents = _out426;
            RAST._IExpr _1802_valueR;
            DCOMP._IOwnership _1803_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1804_valueIdents;
            RAST._IExpr _out427;
            DCOMP._IOwnership _out428;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out429;
            (this).GenExpr(_1795_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out427, out _out428, out _out429);
            _1802_valueR = _out427;
            _1803_valueOwnership = _out428;
            _1804_valueIdents = _out429;
            r = ((_1796_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1799_indexR, _1802_valueR));
            RAST._IExpr _out430;
            DCOMP._IOwnership _out431;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out430, out _out431);
            r = _out430;
            resultingOwnership = _out431;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1798_exprIdents, _1801_indexIdents), _1804_valueIdents);
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_MapUpdate) {
          DAST._IExpression _1805_expr = _source83.dtor_expr;
          DAST._IExpression _1806_index = _source83.dtor_indexExpr;
          DAST._IExpression _1807_value = _source83.dtor_value;
          unmatched83 = false;
          {
            RAST._IExpr _1808_exprR;
            DCOMP._IOwnership _1809___v144;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1810_exprIdents;
            RAST._IExpr _out432;
            DCOMP._IOwnership _out433;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out434;
            (this).GenExpr(_1805_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out432, out _out433, out _out434);
            _1808_exprR = _out432;
            _1809___v144 = _out433;
            _1810_exprIdents = _out434;
            RAST._IExpr _1811_indexR;
            DCOMP._IOwnership _1812_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1813_indexIdents;
            RAST._IExpr _out435;
            DCOMP._IOwnership _out436;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out437;
            (this).GenExpr(_1806_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out435, out _out436, out _out437);
            _1811_indexR = _out435;
            _1812_indexOwnership = _out436;
            _1813_indexIdents = _out437;
            RAST._IExpr _1814_valueR;
            DCOMP._IOwnership _1815_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1816_valueIdents;
            RAST._IExpr _out438;
            DCOMP._IOwnership _out439;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out440;
            (this).GenExpr(_1807_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out438, out _out439, out _out440);
            _1814_valueR = _out438;
            _1815_valueOwnership = _out439;
            _1816_valueIdents = _out440;
            r = ((_1808_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1811_indexR, _1814_valueR));
            RAST._IExpr _out441;
            DCOMP._IOwnership _out442;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out441, out _out442);
            r = _out441;
            resultingOwnership = _out442;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1810_exprIdents, _1813_indexIdents), _1816_valueIdents);
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_This) {
          unmatched83 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source84 = selfIdent;
            bool unmatched84 = true;
            if (unmatched84) {
              if (_source84.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1817_id = _source84.dtor_value;
                unmatched84 = false;
                {
                  r = RAST.Expr.create_Identifier(_1817_id);
                  if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
                    r = RAST.__default.Clone(r);
                    resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
                  } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
                    r = RAST.__default.BoxNew(RAST.__default.Clone(r));
                    resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
                  } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
                    if (!(_1817_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                      r = RAST.__default.Borrow(r);
                    }
                    resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
                  } else {
                    if (!(_1817_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                      r = RAST.__default.BorrowMut(r);
                    }
                    resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
                  }
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1817_id);
                }
              }
            }
            if (unmatched84) {
              unmatched84 = false;
              {
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")"));
                RAST._IExpr _out443;
                DCOMP._IOwnership _out444;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out443, out _out444);
                r = _out443;
                resultingOwnership = _out444;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              }
            }
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_Ite) {
          DAST._IExpression _1818_cond = _source83.dtor_cond;
          DAST._IExpression _1819_t = _source83.dtor_thn;
          DAST._IExpression _1820_f = _source83.dtor_els;
          unmatched83 = false;
          {
            RAST._IExpr _1821_cond;
            DCOMP._IOwnership _1822___v145;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1823_recIdentsCond;
            RAST._IExpr _out445;
            DCOMP._IOwnership _out446;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out447;
            (this).GenExpr(_1818_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out445, out _out446, out _out447);
            _1821_cond = _out445;
            _1822___v145 = _out446;
            _1823_recIdentsCond = _out447;
            Dafny.ISequence<Dafny.Rune> _1824_condString;
            _1824_condString = (_1821_cond)._ToString(DCOMP.__default.IND);
            RAST._IExpr _1825___v146;
            DCOMP._IOwnership _1826_tHasToBeOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1827___v147;
            RAST._IExpr _out448;
            DCOMP._IOwnership _out449;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out450;
            (this).GenExpr(_1819_t, selfIdent, env, expectedOwnership, out _out448, out _out449, out _out450);
            _1825___v146 = _out448;
            _1826_tHasToBeOwned = _out449;
            _1827___v147 = _out450;
            RAST._IExpr _1828_fExpr;
            DCOMP._IOwnership _1829_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1830_recIdentsF;
            RAST._IExpr _out451;
            DCOMP._IOwnership _out452;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out453;
            (this).GenExpr(_1820_f, selfIdent, env, _1826_tHasToBeOwned, out _out451, out _out452, out _out453);
            _1828_fExpr = _out451;
            _1829_fOwned = _out452;
            _1830_recIdentsF = _out453;
            Dafny.ISequence<Dafny.Rune> _1831_fString;
            _1831_fString = (_1828_fExpr)._ToString(DCOMP.__default.IND);
            RAST._IExpr _1832_tExpr;
            DCOMP._IOwnership _1833___v148;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1834_recIdentsT;
            RAST._IExpr _out454;
            DCOMP._IOwnership _out455;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out456;
            (this).GenExpr(_1819_t, selfIdent, env, _1829_fOwned, out _out454, out _out455, out _out456);
            _1832_tExpr = _out454;
            _1833___v148 = _out455;
            _1834_recIdentsT = _out456;
            Dafny.ISequence<Dafny.Rune> _1835_tString;
            _1835_tString = (_1832_tExpr)._ToString(DCOMP.__default.IND);
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _1824_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _1835_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _1831_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})")));
            RAST._IExpr _out457;
            DCOMP._IOwnership _out458;
            DCOMP.COMP.FromOwnership(r, _1829_fOwned, expectedOwnership, out _out457, out _out458);
            r = _out457;
            resultingOwnership = _out458;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1823_recIdentsCond, _1834_recIdentsT), _1830_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source83.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _1836_e = _source83.dtor_expr;
            DAST.Format._IUnaryOpFormat _1837_format = _source83.dtor_format1;
            unmatched83 = false;
            {
              RAST._IExpr _1838_recursiveGen;
              DCOMP._IOwnership _1839___v149;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1840_recIdents;
              RAST._IExpr _out459;
              DCOMP._IOwnership _out460;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out461;
              (this).GenExpr(_1836_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out459, out _out460, out _out461);
              _1838_recursiveGen = _out459;
              _1839___v149 = _out460;
              _1840_recIdents = _out461;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _1838_recursiveGen, _1837_format);
              RAST._IExpr _out462;
              DCOMP._IOwnership _out463;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out462, out _out463);
              r = _out462;
              resultingOwnership = _out463;
              readIdents = _1840_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source83.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _1841_e = _source83.dtor_expr;
            DAST.Format._IUnaryOpFormat _1842_format = _source83.dtor_format1;
            unmatched83 = false;
            {
              RAST._IExpr _1843_recursiveGen;
              DCOMP._IOwnership _1844___v150;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1845_recIdents;
              RAST._IExpr _out464;
              DCOMP._IOwnership _out465;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out466;
              (this).GenExpr(_1841_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out464, out _out465, out _out466);
              _1843_recursiveGen = _out464;
              _1844___v150 = _out465;
              _1845_recIdents = _out466;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _1843_recursiveGen, _1842_format);
              RAST._IExpr _out467;
              DCOMP._IOwnership _out468;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out467, out _out468);
              r = _out467;
              resultingOwnership = _out468;
              readIdents = _1845_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source83.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _1846_e = _source83.dtor_expr;
            DAST.Format._IUnaryOpFormat _1847_format = _source83.dtor_format1;
            unmatched83 = false;
            {
              RAST._IExpr _1848_recursiveGen;
              DCOMP._IOwnership _1849_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1850_recIdents;
              RAST._IExpr _out469;
              DCOMP._IOwnership _out470;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out471;
              (this).GenExpr(_1846_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out469, out _out470, out _out471);
              _1848_recursiveGen = _out469;
              _1849_recOwned = _out470;
              _1850_recIdents = _out471;
              r = ((_1848_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out472;
              DCOMP._IOwnership _out473;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out472, out _out473);
              r = _out472;
              resultingOwnership = _out473;
              readIdents = _1850_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_BinOp) {
          DAST._IBinOp _1851___v151 = _source83.dtor_op;
          DAST._IExpression _1852___v152 = _source83.dtor_left;
          DAST._IExpression _1853___v153 = _source83.dtor_right;
          DAST.Format._IBinaryOpFormat _1854___v154 = _source83.dtor_format2;
          unmatched83 = false;
          RAST._IExpr _out474;
          DCOMP._IOwnership _out475;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out476;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out474, out _out475, out _out476);
          r = _out474;
          resultingOwnership = _out475;
          readIdents = _out476;
        }
      }
      if (unmatched83) {
        if (_source83.is_ArrayLen) {
          DAST._IExpression _1855_expr = _source83.dtor_expr;
          DAST._IType _1856_exprType = _source83.dtor_exprType;
          BigInteger _1857_dim = _source83.dtor_dim;
          bool _1858_native = _source83.dtor_native;
          unmatched83 = false;
          {
            RAST._IExpr _1859_recursiveGen;
            DCOMP._IOwnership _1860___v155;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1861_recIdents;
            RAST._IExpr _out477;
            DCOMP._IOwnership _out478;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out479;
            (this).GenExpr(_1855_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out477, out _out478, out _out479);
            _1859_recursiveGen = _out477;
            _1860___v155 = _out478;
            _1861_recIdents = _out479;
            RAST._IType _1862_arrayType;
            RAST._IType _out480;
            _out480 = (this).GenType(_1856_exprType, false, false);
            _1862_arrayType = _out480;
            if (!((_1862_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _1863_msg;
              _1863_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_1862_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1863_msg);
              r = RAST.Expr.create_RawExpr(_1863_msg);
            } else {
              RAST._IType _1864_underlying;
              _1864_underlying = (_1862_arrayType).ObjectOrPointerUnderlying();
              if (((_1857_dim).Sign == 0) && ((_1864_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_1859_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_1857_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_1859_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = (((this).read__macro).Apply1(_1859_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Length"), Std.Strings.__default.OfNat(_1857_dim)));
                }
              }
              if (!(_1858_native)) {
                r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(r);
              }
            }
            RAST._IExpr _out481;
            DCOMP._IOwnership _out482;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out481, out _out482);
            r = _out481;
            resultingOwnership = _out482;
            readIdents = _1861_recIdents;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_MapKeys) {
          DAST._IExpression _1865_expr = _source83.dtor_expr;
          unmatched83 = false;
          {
            RAST._IExpr _1866_recursiveGen;
            DCOMP._IOwnership _1867___v156;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1868_recIdents;
            RAST._IExpr _out483;
            DCOMP._IOwnership _out484;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out485;
            (this).GenExpr(_1865_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out483, out _out484, out _out485);
            _1866_recursiveGen = _out483;
            _1867___v156 = _out484;
            _1868_recIdents = _out485;
            readIdents = _1868_recIdents;
            r = ((_1866_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out486;
            DCOMP._IOwnership _out487;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out486, out _out487);
            r = _out486;
            resultingOwnership = _out487;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_MapValues) {
          DAST._IExpression _1869_expr = _source83.dtor_expr;
          unmatched83 = false;
          {
            RAST._IExpr _1870_recursiveGen;
            DCOMP._IOwnership _1871___v157;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1872_recIdents;
            RAST._IExpr _out488;
            DCOMP._IOwnership _out489;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out490;
            (this).GenExpr(_1869_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out488, out _out489, out _out490);
            _1870_recursiveGen = _out488;
            _1871___v157 = _out489;
            _1872_recIdents = _out490;
            readIdents = _1872_recIdents;
            r = ((_1870_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out491;
            DCOMP._IOwnership _out492;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out491, out _out492);
            r = _out491;
            resultingOwnership = _out492;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_SelectFn) {
          DAST._IExpression _1873_on = _source83.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1874_field = _source83.dtor_field;
          bool _1875_isDatatype = _source83.dtor_onDatatype;
          bool _1876_isStatic = _source83.dtor_isStatic;
          BigInteger _1877_arity = _source83.dtor_arity;
          unmatched83 = false;
          {
            RAST._IExpr _1878_onExpr;
            DCOMP._IOwnership _1879_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1880_recIdents;
            RAST._IExpr _out493;
            DCOMP._IOwnership _out494;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out495;
            (this).GenExpr(_1873_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out493, out _out494, out _out495);
            _1878_onExpr = _out493;
            _1879_onOwned = _out494;
            _1880_recIdents = _out495;
            Dafny.ISequence<Dafny.Rune> _1881_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _1882_onString;
            _1882_onString = (_1878_onExpr)._ToString(DCOMP.__default.IND);
            if (_1876_isStatic) {
              _1881_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1882_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_1874_field));
            } else {
              _1881_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _1881_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1881_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _1882_onString), ((object.Equals(_1879_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _1883_args;
              _1883_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _1884_i;
              _1884_i = BigInteger.Zero;
              while ((_1884_i) < (_1877_arity)) {
                if ((_1884_i).Sign == 1) {
                  _1883_args = Dafny.Sequence<Dafny.Rune>.Concat(_1883_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _1883_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1883_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_1884_i));
                _1884_i = (_1884_i) + (BigInteger.One);
              }
              _1881_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1881_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _1883_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _1881_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1881_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_1874_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1883_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _1881_s = Dafny.Sequence<Dafny.Rune>.Concat(_1881_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _1881_s = Dafny.Sequence<Dafny.Rune>.Concat(_1881_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _1885_typeShape;
            _1885_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _1886_i;
            _1886_i = BigInteger.Zero;
            while ((_1886_i) < (_1877_arity)) {
              if ((_1886_i).Sign == 1) {
                _1885_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1885_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _1885_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1885_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _1886_i = (_1886_i) + (BigInteger.One);
            }
            _1885_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1885_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _1881_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _1881_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _1885_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_1881_s);
            RAST._IExpr _out496;
            DCOMP._IOwnership _out497;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out496, out _out497);
            r = _out496;
            resultingOwnership = _out497;
            readIdents = _1880_recIdents;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_Select) {
          DAST._IExpression expr0 = _source83.dtor_expr;
          if (expr0.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1887_c = expr0.dtor_Companion_a0;
            Dafny.ISequence<Dafny.Rune> _1888_field = _source83.dtor_field;
            bool _1889_isConstant = _source83.dtor_isConstant;
            bool _1890_isDatatype = _source83.dtor_onDatatype;
            DAST._IType _1891_fieldType = _source83.dtor_fieldType;
            unmatched83 = false;
            {
              RAST._IExpr _1892_onExpr;
              DCOMP._IOwnership _1893_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1894_recIdents;
              RAST._IExpr _out498;
              DCOMP._IOwnership _out499;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out500;
              (this).GenExpr(DAST.Expression.create_Companion(_1887_c), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out498, out _out499, out _out500);
              _1892_onExpr = _out498;
              _1893_onOwned = _out499;
              _1894_recIdents = _out500;
              r = ((_1892_onExpr).MSel(DCOMP.__default.escapeName(_1888_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out501;
              DCOMP._IOwnership _out502;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out501, out _out502);
              r = _out501;
              resultingOwnership = _out502;
              readIdents = _1894_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_Select) {
          DAST._IExpression _1895_on = _source83.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1896_field = _source83.dtor_field;
          bool _1897_isConstant = _source83.dtor_isConstant;
          bool _1898_isDatatype = _source83.dtor_onDatatype;
          DAST._IType _1899_fieldType = _source83.dtor_fieldType;
          unmatched83 = false;
          {
            if (_1898_isDatatype) {
              RAST._IExpr _1900_onExpr;
              DCOMP._IOwnership _1901_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1902_recIdents;
              RAST._IExpr _out503;
              DCOMP._IOwnership _out504;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out505;
              (this).GenExpr(_1895_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out503, out _out504, out _out505);
              _1900_onExpr = _out503;
              _1901_onOwned = _out504;
              _1902_recIdents = _out505;
              r = ((_1900_onExpr).Sel(DCOMP.__default.escapeName(_1896_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _1903_typ;
              RAST._IType _out506;
              _out506 = (this).GenType(_1899_fieldType, false, false);
              _1903_typ = _out506;
              RAST._IExpr _out507;
              DCOMP._IOwnership _out508;
              DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out507, out _out508);
              r = _out507;
              resultingOwnership = _out508;
              readIdents = _1902_recIdents;
            } else {
              RAST._IExpr _1904_onExpr;
              DCOMP._IOwnership _1905_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1906_recIdents;
              RAST._IExpr _out509;
              DCOMP._IOwnership _out510;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out511;
              (this).GenExpr(_1895_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out509, out _out510, out _out511);
              _1904_onExpr = _out509;
              _1905_onOwned = _out510;
              _1906_recIdents = _out511;
              r = _1904_onExpr;
              if (!object.Equals(_1904_onExpr, RAST.__default.self)) {
                RAST._IExpr _source85 = _1904_onExpr;
                bool unmatched85 = true;
                if (unmatched85) {
                  if (_source85.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> op16 = _source85.dtor_op1;
                    if (object.Equals(op16, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                      RAST._IExpr underlying6 = _source85.dtor_underlying;
                      if (underlying6.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name14 = underlying6.dtor_name;
                        if (object.Equals(name14, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                          DAST.Format._IUnaryOpFormat _1907___v158 = _source85.dtor_format;
                          unmatched85 = false;
                          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
                        }
                      }
                    }
                  }
                }
                if (unmatched85) {
                  RAST._IExpr _1908___v159 = _source85;
                  unmatched85 = false;
                }
                r = ((this).read__macro).Apply1(r);
              }
              r = (r).Sel(DCOMP.__default.escapeName(_1896_field));
              if (_1897_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              DCOMP._IOwnership _1909_fromOwnership;
              _1909_fromOwnership = ((_1897_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out512;
              DCOMP._IOwnership _out513;
              DCOMP.COMP.FromOwnership(r, _1909_fromOwnership, expectedOwnership, out _out512, out _out513);
              r = _out512;
              resultingOwnership = _out513;
              readIdents = _1906_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_Index) {
          DAST._IExpression _1910_on = _source83.dtor_expr;
          DAST._ICollKind _1911_collKind = _source83.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _1912_indices = _source83.dtor_indices;
          unmatched83 = false;
          {
            RAST._IExpr _1913_onExpr;
            DCOMP._IOwnership _1914_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1915_recIdents;
            RAST._IExpr _out514;
            DCOMP._IOwnership _out515;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out516;
            (this).GenExpr(_1910_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out514, out _out515, out _out516);
            _1913_onExpr = _out514;
            _1914_onOwned = _out515;
            _1915_recIdents = _out516;
            readIdents = _1915_recIdents;
            r = _1913_onExpr;
            BigInteger _1916_i;
            _1916_i = BigInteger.Zero;
            while ((_1916_i) < (new BigInteger((_1912_indices).Count))) {
              if (object.Equals(_1911_collKind, DAST.CollKind.create_Array())) {
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              RAST._IExpr _1917_idx;
              DCOMP._IOwnership _1918_idxOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1919_recIdentsIdx;
              RAST._IExpr _out517;
              DCOMP._IOwnership _out518;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out519;
              (this).GenExpr((_1912_indices).Select(_1916_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out517, out _out518, out _out519);
              _1917_idx = _out517;
              _1918_idxOwned = _out518;
              _1919_recIdentsIdx = _out519;
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_1917_idx);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1919_recIdentsIdx);
              _1916_i = (_1916_i) + (BigInteger.One);
            }
            RAST._IExpr _out520;
            DCOMP._IOwnership _out521;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out520, out _out521);
            r = _out520;
            resultingOwnership = _out521;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_IndexRange) {
          DAST._IExpression _1920_on = _source83.dtor_expr;
          bool _1921_isArray = _source83.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _1922_low = _source83.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _1923_high = _source83.dtor_high;
          unmatched83 = false;
          {
            RAST._IExpr _1924_onExpr;
            DCOMP._IOwnership _1925_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1926_recIdents;
            RAST._IExpr _out522;
            DCOMP._IOwnership _out523;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out524;
            (this).GenExpr(_1920_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out522, out _out523, out _out524);
            _1924_onExpr = _out522;
            _1925_onOwned = _out523;
            _1926_recIdents = _out524;
            readIdents = _1926_recIdents;
            Dafny.ISequence<Dafny.Rune> _1927_methodName;
            _1927_methodName = (((_1922_low).is_Some) ? ((((_1923_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_1923_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _1928_arguments;
            _1928_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source86 = _1922_low;
            bool unmatched86 = true;
            if (unmatched86) {
              if (_source86.is_Some) {
                DAST._IExpression _1929_l = _source86.dtor_value;
                unmatched86 = false;
                {
                  RAST._IExpr _1930_lExpr;
                  DCOMP._IOwnership _1931___v160;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1932_recIdentsL;
                  RAST._IExpr _out525;
                  DCOMP._IOwnership _out526;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out527;
                  (this).GenExpr(_1929_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out525, out _out526, out _out527);
                  _1930_lExpr = _out525;
                  _1931___v160 = _out526;
                  _1932_recIdentsL = _out527;
                  _1928_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1928_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1930_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1932_recIdentsL);
                }
              }
            }
            if (unmatched86) {
              unmatched86 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source87 = _1923_high;
            bool unmatched87 = true;
            if (unmatched87) {
              if (_source87.is_Some) {
                DAST._IExpression _1933_h = _source87.dtor_value;
                unmatched87 = false;
                {
                  RAST._IExpr _1934_hExpr;
                  DCOMP._IOwnership _1935___v161;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1936_recIdentsH;
                  RAST._IExpr _out528;
                  DCOMP._IOwnership _out529;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out530;
                  (this).GenExpr(_1933_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out528, out _out529, out _out530);
                  _1934_hExpr = _out528;
                  _1935___v161 = _out529;
                  _1936_recIdentsH = _out530;
                  _1928_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1928_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1934_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1936_recIdentsH);
                }
              }
            }
            if (unmatched87) {
              unmatched87 = false;
            }
            r = _1924_onExpr;
            if (_1921_isArray) {
              if (!(_1927_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _1927_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1927_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _1927_methodName))).Apply(_1928_arguments);
            } else {
              if (!(_1927_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_1927_methodName)).Apply(_1928_arguments);
              }
            }
            RAST._IExpr _out531;
            DCOMP._IOwnership _out532;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out531, out _out532);
            r = _out531;
            resultingOwnership = _out532;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_TupleSelect) {
          DAST._IExpression _1937_on = _source83.dtor_expr;
          BigInteger _1938_idx = _source83.dtor_index;
          DAST._IType _1939_fieldType = _source83.dtor_fieldType;
          unmatched83 = false;
          {
            RAST._IExpr _1940_onExpr;
            DCOMP._IOwnership _1941_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1942_recIdents;
            RAST._IExpr _out533;
            DCOMP._IOwnership _out534;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out535;
            (this).GenExpr(_1937_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out533, out _out534, out _out535);
            _1940_onExpr = _out533;
            _1941_onOwnership = _out534;
            _1942_recIdents = _out535;
            Dafny.ISequence<Dafny.Rune> _1943_selName;
            _1943_selName = Std.Strings.__default.OfNat(_1938_idx);
            DAST._IType _source88 = _1939_fieldType;
            bool unmatched88 = true;
            if (unmatched88) {
              if (_source88.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1944_tps = _source88.dtor_Tuple_a0;
                unmatched88 = false;
                if (((_1939_fieldType).is_Tuple) && ((new BigInteger((_1944_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _1943_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1943_selName);
                }
              }
            }
            if (unmatched88) {
              DAST._IType _1945___v162 = _source88;
              unmatched88 = false;
            }
            r = (_1940_onExpr).Sel(_1943_selName);
            RAST._IExpr _out536;
            DCOMP._IOwnership _out537;
            DCOMP.COMP.FromOwnership(r, _1941_onOwnership, expectedOwnership, out _out536, out _out537);
            r = _out536;
            resultingOwnership = _out537;
            readIdents = _1942_recIdents;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_Call) {
          DAST._IExpression _1946_on = _source83.dtor_on;
          DAST._ICallName _1947_name = _source83.dtor_callName;
          Dafny.ISequence<DAST._IType> _1948_typeArgs = _source83.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1949_args = _source83.dtor_args;
          unmatched83 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IExpr _1950_onExpr;
            DCOMP._IOwnership _1951___v163;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1952_recIdents;
            RAST._IExpr _out538;
            DCOMP._IOwnership _out539;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out540;
            (this).GenExpr(_1946_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out538, out _out539, out _out540);
            _1950_onExpr = _out538;
            _1951___v163 = _out539;
            _1952_recIdents = _out540;
            Dafny.ISequence<RAST._IType> _1953_typeExprs;
            _1953_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
            if ((new BigInteger((_1948_typeArgs).Count)) >= (BigInteger.One)) {
              BigInteger _hi39 = new BigInteger((_1948_typeArgs).Count);
              for (BigInteger _1954_typeI = BigInteger.Zero; _1954_typeI < _hi39; _1954_typeI++) {
                RAST._IType _1955_typeExpr;
                RAST._IType _out541;
                _out541 = (this).GenType((_1948_typeArgs).Select(_1954_typeI), false, false);
                _1955_typeExpr = _out541;
                _1953_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1953_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1955_typeExpr));
              }
            }
            Dafny.ISequence<RAST._IExpr> _1956_argExprs;
            _1956_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi40 = new BigInteger((_1949_args).Count);
            for (BigInteger _1957_i = BigInteger.Zero; _1957_i < _hi40; _1957_i++) {
              DCOMP._IOwnership _1958_argOwnership;
              _1958_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              if (((_1947_name).is_CallName) && ((_1957_i) < (new BigInteger((((_1947_name).dtor_signature)).Count)))) {
                RAST._IType _1959_tpe;
                RAST._IType _out542;
                _out542 = (this).GenType(((((_1947_name).dtor_signature)).Select(_1957_i)).dtor_typ, false, false);
                _1959_tpe = _out542;
                if ((_1959_tpe).CanReadWithoutClone()) {
                  _1958_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
                }
              }
              RAST._IExpr _1960_argExpr;
              DCOMP._IOwnership _1961___v164;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1962_argIdents;
              RAST._IExpr _out543;
              DCOMP._IOwnership _out544;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out545;
              (this).GenExpr((_1949_args).Select(_1957_i), selfIdent, env, _1958_argOwnership, out _out543, out _out544, out _out545);
              _1960_argExpr = _out543;
              _1961___v164 = _out544;
              _1962_argIdents = _out545;
              _1956_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1956_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1960_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1962_argIdents);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1952_recIdents);
            Dafny.ISequence<Dafny.Rune> _1963_renderedName;
            _1963_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
              DAST._ICallName _source89 = _1947_name;
              bool unmatched89 = true;
              if (unmatched89) {
                if (_source89.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _1964_ident = _source89.dtor_name;
                  Std.Wrappers._IOption<DAST._IType> _1965___v165 = _source89.dtor_onType;
                  Dafny.ISequence<DAST._IFormal> _1966___v166 = _source89.dtor_signature;
                  unmatched89 = false;
                  return DCOMP.__default.escapeName(_1964_ident);
                }
              }
              if (unmatched89) {
                bool disjunctiveMatch13 = false;
                if (_source89.is_MapBuilderAdd) {
                  disjunctiveMatch13 = true;
                }
                if (_source89.is_SetBuilderAdd) {
                  disjunctiveMatch13 = true;
                }
                if (disjunctiveMatch13) {
                  unmatched89 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                }
              }
              if (unmatched89) {
                bool disjunctiveMatch14 = false;
                disjunctiveMatch14 = true;
                disjunctiveMatch14 = true;
                if (disjunctiveMatch14) {
                  unmatched89 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                }
              }
              throw new System.Exception("unexpected control point");
            }))();
            DAST._IExpression _source90 = _1946_on;
            bool unmatched90 = true;
            if (unmatched90) {
              if (_source90.is_Companion) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1967___v167 = _source90.dtor_Companion_a0;
                unmatched90 = false;
                {
                  _1950_onExpr = (_1950_onExpr).MSel(_1963_renderedName);
                }
              }
            }
            if (unmatched90) {
              DAST._IExpression _1968___v168 = _source90;
              unmatched90 = false;
              {
                if (!object.Equals(_1950_onExpr, RAST.__default.self)) {
                  DAST._ICallName _source91 = _1947_name;
                  bool unmatched91 = true;
                  if (unmatched91) {
                    if (_source91.is_CallName) {
                      Dafny.ISequence<Dafny.Rune> _1969___v169 = _source91.dtor_name;
                      Std.Wrappers._IOption<DAST._IType> onType1 = _source91.dtor_onType;
                      if (onType1.is_Some) {
                        DAST._IType _1970_tpe = onType1.dtor_value;
                        Dafny.ISequence<DAST._IFormal> _1971___v170 = _source91.dtor_signature;
                        unmatched91 = false;
                        RAST._IType _1972_typ;
                        RAST._IType _out546;
                        _out546 = (this).GenType(_1970_tpe, false, false);
                        _1972_typ = _out546;
                        if ((_1972_typ).IsObjectOrPointer()) {
                          _1950_onExpr = ((this).read__macro).Apply1(_1950_onExpr);
                        }
                      }
                    }
                  }
                  if (unmatched91) {
                    DAST._ICallName _1973___v171 = _source91;
                    unmatched91 = false;
                  }
                }
                _1950_onExpr = (_1950_onExpr).Sel(_1963_renderedName);
              }
            }
            r = _1950_onExpr;
            if ((new BigInteger((_1953_typeExprs).Count)).Sign == 1) {
              r = (r).ApplyType(_1953_typeExprs);
            }
            r = (r).Apply(_1956_argExprs);
            RAST._IExpr _out547;
            DCOMP._IOwnership _out548;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out547, out _out548);
            r = _out547;
            resultingOwnership = _out548;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _1974_paramsDafny = _source83.dtor_params;
          DAST._IType _1975_retType = _source83.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _1976_body = _source83.dtor_body;
          unmatched83 = false;
          {
            Dafny.ISequence<RAST._IFormal> _1977_params;
            Dafny.ISequence<RAST._IFormal> _out549;
            _out549 = (this).GenParams(_1974_paramsDafny);
            _1977_params = _out549;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1978_paramNames;
            _1978_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1979_paramTypesMap;
            _1979_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi41 = new BigInteger((_1977_params).Count);
            for (BigInteger _1980_i = BigInteger.Zero; _1980_i < _hi41; _1980_i++) {
              Dafny.ISequence<Dafny.Rune> _1981_name;
              _1981_name = ((_1977_params).Select(_1980_i)).dtor_name;
              _1978_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1978_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1981_name));
              _1979_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1979_paramTypesMap, _1981_name, ((_1977_params).Select(_1980_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _1982_env;
            _1982_env = DCOMP.Environment.create(_1978_paramNames, _1979_paramTypesMap);
            RAST._IExpr _1983_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1984_recIdents;
            DCOMP._IEnvironment _1985___v172;
            RAST._IExpr _out550;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out551;
            DCOMP._IEnvironment _out552;
            (this).GenStmts(_1976_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), _1982_env, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out550, out _out551, out _out552);
            _1983_recursiveGen = _out550;
            _1984_recIdents = _out551;
            _1985___v172 = _out552;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _1984_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1984_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_1986_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll6 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in (_1986_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _1987_name = (Dafny.ISequence<Dafny.Rune>)_compr_6;
                if ((_1986_paramNames).Contains(_1987_name)) {
                  _coll6.Add(_1987_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll6);
            }))())(_1978_paramNames));
            RAST._IExpr _1988_allReadCloned;
            _1988_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_1984_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _1989_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_1984_recIdents).Elements) {
                _1989_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_1984_recIdents).Contains(_1989_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 4231)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) && ((_1989_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
                  _1988_allReadCloned = (_1988_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
                }
              } else if (!((_1978_paramNames).Contains(_1989_next))) {
                _1988_allReadCloned = (_1988_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1989_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.Expr.create_Identifier(_1989_next)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1989_next));
              }
              _1984_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1984_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1989_next));
            }
            RAST._IType _1990_retTypeGen;
            RAST._IType _out553;
            _out553 = (this).GenType(_1975_retType, false, true);
            _1990_retTypeGen = _out553;
            r = RAST.Expr.create_Block((_1988_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_1977_params, Std.Wrappers.Option<RAST._IType>.create_Some(_1990_retTypeGen), RAST.Expr.create_Block(_1983_recursiveGen)))));
            RAST._IExpr _out554;
            DCOMP._IOwnership _out555;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out554, out _out555);
            r = _out554;
            resultingOwnership = _out555;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _1991_values = _source83.dtor_values;
          DAST._IType _1992_retType = _source83.dtor_retType;
          DAST._IExpression _1993_expr = _source83.dtor_expr;
          unmatched83 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1994_paramNames;
            _1994_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _1995_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out556;
            _out556 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_1996_value) => {
              return (_1996_value).dtor__0;
            })), _1991_values));
            _1995_paramFormals = _out556;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1997_paramTypes;
            _1997_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1998_paramNamesSet;
            _1998_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi42 = new BigInteger((_1991_values).Count);
            for (BigInteger _1999_i = BigInteger.Zero; _1999_i < _hi42; _1999_i++) {
              Dafny.ISequence<Dafny.Rune> _2000_name;
              _2000_name = (((_1991_values).Select(_1999_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2001_rName;
              _2001_rName = DCOMP.__default.escapeName(_2000_name);
              _1994_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1994_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2001_rName));
              _1997_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1997_paramTypes, _2001_rName, ((_1995_paramFormals).Select(_1999_i)).dtor_tpe);
              _1998_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1998_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2001_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi43 = new BigInteger((_1991_values).Count);
            for (BigInteger _2002_i = BigInteger.Zero; _2002_i < _hi43; _2002_i++) {
              RAST._IType _2003_typeGen;
              RAST._IType _out557;
              _out557 = (this).GenType((((_1991_values).Select(_2002_i)).dtor__0).dtor_typ, false, true);
              _2003_typeGen = _out557;
              RAST._IExpr _2004_valueGen;
              DCOMP._IOwnership _2005___v173;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2006_recIdents;
              RAST._IExpr _out558;
              DCOMP._IOwnership _out559;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out560;
              (this).GenExpr(((_1991_values).Select(_2002_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out558, out _out559, out _out560);
              _2004_valueGen = _out558;
              _2005___v173 = _out559;
              _2006_recIdents = _out560;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_1991_values).Select(_2002_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2003_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2004_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2006_recIdents);
            }
            DCOMP._IEnvironment _2007_newEnv;
            _2007_newEnv = DCOMP.Environment.create(_1994_paramNames, _1997_paramTypes);
            RAST._IExpr _2008_recGen;
            DCOMP._IOwnership _2009_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2010_recIdents;
            RAST._IExpr _out561;
            DCOMP._IOwnership _out562;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out563;
            (this).GenExpr(_1993_expr, selfIdent, _2007_newEnv, expectedOwnership, out _out561, out _out562, out _out563);
            _2008_recGen = _out561;
            _2009_recOwned = _out562;
            _2010_recIdents = _out563;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2010_recIdents, _1998_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2008_recGen));
            RAST._IExpr _out564;
            DCOMP._IOwnership _out565;
            DCOMP.COMP.FromOwnership(r, _2009_recOwned, expectedOwnership, out _out564, out _out565);
            r = _out564;
            resultingOwnership = _out565;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2011_name = _source83.dtor_name;
          DAST._IType _2012_tpe = _source83.dtor_typ;
          DAST._IExpression _2013_value = _source83.dtor_value;
          DAST._IExpression _2014_iifeBody = _source83.dtor_iifeBody;
          unmatched83 = false;
          {
            RAST._IExpr _2015_valueGen;
            DCOMP._IOwnership _2016___v174;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2017_recIdents;
            RAST._IExpr _out566;
            DCOMP._IOwnership _out567;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out568;
            (this).GenExpr(_2013_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out566, out _out567, out _out568);
            _2015_valueGen = _out566;
            _2016___v174 = _out567;
            _2017_recIdents = _out568;
            readIdents = _2017_recIdents;
            RAST._IType _2018_valueTypeGen;
            RAST._IType _out569;
            _out569 = (this).GenType(_2012_tpe, false, true);
            _2018_valueTypeGen = _out569;
            RAST._IExpr _2019_bodyGen;
            DCOMP._IOwnership _2020___v175;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2021_bodyIdents;
            RAST._IExpr _out570;
            DCOMP._IOwnership _out571;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out572;
            (this).GenExpr(_2014_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out570, out _out571, out _out572);
            _2019_bodyGen = _out570;
            _2020___v175 = _out571;
            _2021_bodyIdents = _out572;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2021_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_2011_name)))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_2011_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_2018_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2015_valueGen))).Then(_2019_bodyGen));
            RAST._IExpr _out573;
            DCOMP._IOwnership _out574;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out573, out _out574);
            r = _out573;
            resultingOwnership = _out574;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_Apply) {
          DAST._IExpression _2022_func = _source83.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2023_args = _source83.dtor_args;
          unmatched83 = false;
          {
            RAST._IExpr _2024_funcExpr;
            DCOMP._IOwnership _2025___v176;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2026_recIdents;
            RAST._IExpr _out575;
            DCOMP._IOwnership _out576;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out577;
            (this).GenExpr(_2022_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out575, out _out576, out _out577);
            _2024_funcExpr = _out575;
            _2025___v176 = _out576;
            _2026_recIdents = _out577;
            readIdents = _2026_recIdents;
            Dafny.ISequence<RAST._IExpr> _2027_rArgs;
            _2027_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi44 = new BigInteger((_2023_args).Count);
            for (BigInteger _2028_i = BigInteger.Zero; _2028_i < _hi44; _2028_i++) {
              RAST._IExpr _2029_argExpr;
              DCOMP._IOwnership _2030_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2031_argIdents;
              RAST._IExpr _out578;
              DCOMP._IOwnership _out579;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out580;
              (this).GenExpr((_2023_args).Select(_2028_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out578, out _out579, out _out580);
              _2029_argExpr = _out578;
              _2030_argOwned = _out579;
              _2031_argIdents = _out580;
              _2027_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2027_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2029_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2031_argIdents);
            }
            r = (_2024_funcExpr).Apply(_2027_rArgs);
            RAST._IExpr _out581;
            DCOMP._IOwnership _out582;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out581, out _out582);
            r = _out581;
            resultingOwnership = _out582;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_TypeTest) {
          DAST._IExpression _2032_on = _source83.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2033_dType = _source83.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2034_variant = _source83.dtor_variant;
          unmatched83 = false;
          {
            RAST._IExpr _2035_exprGen;
            DCOMP._IOwnership _2036___v177;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2037_recIdents;
            RAST._IExpr _out583;
            DCOMP._IOwnership _out584;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out585;
            (this).GenExpr(_2032_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out583, out _out584, out _out585);
            _2035_exprGen = _out583;
            _2036___v177 = _out584;
            _2037_recIdents = _out585;
            RAST._IType _2038_dTypePath;
            RAST._IType _out586;
            _out586 = DCOMP.COMP.GenPath(_2033_dType);
            _2038_dTypePath = _out586;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2035_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_2038_dTypePath).MSel(DCOMP.__default.escapeName(_2034_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out587;
            DCOMP._IOwnership _out588;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out587, out _out588);
            r = _out587;
            resultingOwnership = _out588;
            readIdents = _2037_recIdents;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_BoolBoundedPool) {
          unmatched83 = false;
          {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
            RAST._IExpr _out589;
            DCOMP._IOwnership _out590;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out589, out _out590);
            r = _out589;
            resultingOwnership = _out590;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_SetBoundedPool) {
          DAST._IExpression _2039_of = _source83.dtor_of;
          unmatched83 = false;
          {
            RAST._IExpr _2040_exprGen;
            DCOMP._IOwnership _2041___v178;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2042_recIdents;
            RAST._IExpr _out591;
            DCOMP._IOwnership _out592;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out593;
            (this).GenExpr(_2039_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out591, out _out592, out _out593);
            _2040_exprGen = _out591;
            _2041___v178 = _out592;
            _2042_recIdents = _out593;
            r = ((((_2040_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out594;
            DCOMP._IOwnership _out595;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out594, out _out595);
            r = _out594;
            resultingOwnership = _out595;
            readIdents = _2042_recIdents;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_SeqBoundedPool) {
          DAST._IExpression _2043_of = _source83.dtor_of;
          bool _2044_includeDuplicates = _source83.dtor_includeDuplicates;
          unmatched83 = false;
          {
            RAST._IExpr _2045_exprGen;
            DCOMP._IOwnership _2046___v179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2047_recIdents;
            RAST._IExpr _out596;
            DCOMP._IOwnership _out597;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out598;
            (this).GenExpr(_2043_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out596, out _out597, out _out598);
            _2045_exprGen = _out596;
            _2046___v179 = _out597;
            _2047_recIdents = _out598;
            r = ((_2045_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2044_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out599;
            DCOMP._IOwnership _out600;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out599, out _out600);
            r = _out599;
            resultingOwnership = _out600;
            readIdents = _2047_recIdents;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_IntRange) {
          DAST._IExpression _2048_lo = _source83.dtor_lo;
          DAST._IExpression _2049_hi = _source83.dtor_hi;
          bool _2050_up = _source83.dtor_up;
          unmatched83 = false;
          {
            RAST._IExpr _2051_lo;
            DCOMP._IOwnership _2052___v180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2053_recIdentsLo;
            RAST._IExpr _out601;
            DCOMP._IOwnership _out602;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out603;
            (this).GenExpr(_2048_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out601, out _out602, out _out603);
            _2051_lo = _out601;
            _2052___v180 = _out602;
            _2053_recIdentsLo = _out603;
            RAST._IExpr _2054_hi;
            DCOMP._IOwnership _2055___v181;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2056_recIdentsHi;
            RAST._IExpr _out604;
            DCOMP._IOwnership _out605;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out606;
            (this).GenExpr(_2049_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out604, out _out605, out _out606);
            _2054_hi = _out604;
            _2055___v181 = _out605;
            _2056_recIdentsHi = _out606;
            if (_2050_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2051_lo, _2054_hi));
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2054_hi, _2051_lo));
            }
            RAST._IExpr _out607;
            DCOMP._IOwnership _out608;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out607, out _out608);
            r = _out607;
            resultingOwnership = _out608;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2053_recIdentsLo, _2056_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_UnboundedIntRange) {
          DAST._IExpression _2057_start = _source83.dtor_start;
          bool _2058_up = _source83.dtor_up;
          unmatched83 = false;
          {
            RAST._IExpr _2059_start;
            DCOMP._IOwnership _2060___v182;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2061_recIdentStart;
            RAST._IExpr _out609;
            DCOMP._IOwnership _out610;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out611;
            (this).GenExpr(_2057_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out609, out _out610, out _out611);
            _2059_start = _out609;
            _2060___v182 = _out610;
            _2061_recIdentStart = _out611;
            if (_2058_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).Apply1(_2059_start);
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).Apply1(_2059_start);
            }
            RAST._IExpr _out612;
            DCOMP._IOwnership _out613;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out612, out _out613);
            r = _out612;
            resultingOwnership = _out613;
            readIdents = _2061_recIdentStart;
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_MapBuilder) {
          DAST._IType _2062_keyType = _source83.dtor_keyType;
          DAST._IType _2063_valueType = _source83.dtor_valueType;
          unmatched83 = false;
          {
            RAST._IType _2064_kType;
            RAST._IType _out614;
            _out614 = (this).GenType(_2062_keyType, false, false);
            _2064_kType = _out614;
            RAST._IType _2065_vType;
            RAST._IType _out615;
            _out615 = (this).GenType(_2063_valueType, false, false);
            _2065_vType = _out615;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2064_kType, _2065_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out616;
            DCOMP._IOwnership _out617;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out616, out _out617);
            r = _out616;
            resultingOwnership = _out617;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_SetBuilder) {
          DAST._IType _2066_elemType = _source83.dtor_elemType;
          unmatched83 = false;
          {
            RAST._IType _2067_eType;
            RAST._IType _out618;
            _out618 = (this).GenType(_2066_elemType, false, false);
            _2067_eType = _out618;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2067_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out619;
            DCOMP._IOwnership _out620;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out619, out _out620);
            r = _out619;
            resultingOwnership = _out620;
            return ;
          }
        }
      }
      if (unmatched83) {
        DAST._IType _2068_elemType = _source83.dtor_elemType;
        DAST._IExpression _2069_collection = _source83.dtor_collection;
        bool _2070_is__forall = _source83.dtor_is__forall;
        DAST._IExpression _2071_lambda = _source83.dtor_lambda;
        unmatched83 = false;
        {
          RAST._IType _2072_tpe;
          RAST._IType _out621;
          _out621 = (this).GenType(_2068_elemType, false, false);
          _2072_tpe = _out621;
          RAST._IExpr _2073_collectionGen;
          DCOMP._IOwnership _2074___v183;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2075_recIdents;
          RAST._IExpr _out622;
          DCOMP._IOwnership _out623;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out624;
          (this).GenExpr(_2069_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out622, out _out623, out _out624);
          _2073_collectionGen = _out622;
          _2074___v183 = _out623;
          _2075_recIdents = _out624;
          if ((_2071_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2076_formals;
            _2076_formals = (_2071_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2077_newFormals;
            _2077_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi45 = new BigInteger((_2076_formals).Count);
            for (BigInteger _2078_i = BigInteger.Zero; _2078_i < _hi45; _2078_i++) {
              var _pat_let_tv106 = _2076_formals;
              _2077_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2077_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2076_formals).Select(_2078_i), _pat_let13_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let13_0, _2079_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned), ((_pat_let_tv106).Select(_2078_i)).dtor_attributes), _pat_let14_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let14_0, _2080_dt__update_hattributes_h0 => DAST.Formal.create((_2079_dt__update__tmp_h0).dtor_name, (_2079_dt__update__tmp_h0).dtor_typ, _2080_dt__update_hattributes_h0)))))));
            }
            var _pat_let_tv107 = _2077_newFormals;
            DAST._IExpression _2081_newLambda;
            _2081_newLambda = Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_2071_lambda, _pat_let15_0 => Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_pat_let15_0, _2082_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let_tv107, _pat_let16_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let16_0, _2083_dt__update_hparams_h0 => DAST.Expression.create_Lambda(_2083_dt__update_hparams_h0, (_2082_dt__update__tmp_h1).dtor_retType, (_2082_dt__update__tmp_h1).dtor_body)))));
            RAST._IExpr _2084_lambdaGen;
            DCOMP._IOwnership _2085___v184;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2086_recLambdaIdents;
            RAST._IExpr _out625;
            DCOMP._IOwnership _out626;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out627;
            (this).GenExpr(_2081_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out625, out _out626, out _out627);
            _2084_lambdaGen = _out625;
            _2085___v184 = _out626;
            _2086_recLambdaIdents = _out627;
            Dafny.ISequence<Dafny.Rune> _2087_fn;
            _2087_fn = ((_2070_is__forall) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any")));
            r = ((_2073_collectionGen).Sel(_2087_fn)).Apply1(((_2084_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2075_recIdents, _2086_recLambdaIdents);
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Quantifier without an inline lambda"));
            r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
          RAST._IExpr _out628;
          DCOMP._IOwnership _out629;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out628, out _out629);
          r = _out628;
          resultingOwnership = _out629;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      BigInteger _2088_i;
      _2088_i = BigInteger.Zero;
      while ((_2088_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _2089_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _2090_m;
        RAST._IMod _out630;
        _out630 = (this).GenModule((p).Select(_2088_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2090_m = _out630;
        _2089_generated = (_2090_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_2088_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2089_generated);
        _2088_i = (_2088_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2091_i;
      _2091_i = BigInteger.Zero;
      while ((_2091_i) < (new BigInteger((fullName).Count))) {
        if ((_2091_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2091_i)));
        _2091_i = (_2091_i) + (BigInteger.One);
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
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("allocate_rcmut");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> allocate__fn { get {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), (this).allocate);
    } }
    public Dafny.ISequence<Dafny.Rune> update__field__uninit__macro { get {
      if (((this).ObjectType).is_RawPointers) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_uninit!");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_uninit_rcmut!");
      }
    } }
    public RAST._IExpr thisInConstructor { get {
      if (((this).ObjectType).is_RawPointers) {
        return RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
      } else {
        return ((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
    } }
    public Dafny.ISequence<Dafny.Rune> array__construct { get {
      if (((this).ObjectType).is_RawPointers) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("construct");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("construct_rcmut");
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
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("placebos_usize_rcmut");
      }
    } }
    public static Dafny.IMap<DAST._IBinOp,Dafny.ISequence<Dafny.Rune>> OpTable { get {
      return Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.FromElements(new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Mod(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_And(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Or(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("||")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Div(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Lt(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_LtChar(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Plus(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Minus(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Times(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseAnd(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseOr(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseXor(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftRight(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftLeft(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<")));
    } }
  }
} // end of namespace DCOMP