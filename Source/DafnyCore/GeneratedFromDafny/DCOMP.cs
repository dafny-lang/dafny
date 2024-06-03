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
      Dafny.ISequence<Dafny.Rune> _1059___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1059___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1059___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1059___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in123 = (i).Drop(new BigInteger(2));
        i = _in123;
        goto TAIL_CALL_START;
      } else {
        _1059___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1059___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in124 = (i).Drop(BigInteger.One);
        i = _in124;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1060___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1060___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1060___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1060___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in125 = (i).Drop(BigInteger.One);
        i = _in125;
        goto TAIL_CALL_START;
      } else {
        _1060___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1060___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _1061_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1061_r);
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
      BigInteger _1062_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1062_indexInEnv), ((this).dtor_names).Drop((_1062_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
      Dafny.ISequence<Dafny.Rune> _1063_modName;
      _1063_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_1063_modName);
      } else {
        Dafny.ISequence<RAST._IModDecl> _1064_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _1064_body = _out15;
        s = RAST.Mod.create_Mod(_1063_modName, _1064_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi5 = new BigInteger((body).Count);
      for (BigInteger _1065_i = BigInteger.Zero; _1065_i < _hi5; _1065_i++) {
        Dafny.ISequence<RAST._IModDecl> _1066_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source47 = (body).Select(_1065_i);
        bool unmatched47 = true;
        if (unmatched47) {
          if (_source47.is_Module) {
            DAST._IModule _1067_m = _source47.dtor_Module_a0;
            unmatched47 = false;
            RAST._IMod _1068_mm;
            RAST._IMod _out16;
            _out16 = (this).GenModule(_1067_m, containingPath);
            _1068_mm = _out16;
            _1066_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1068_mm));
          }
        }
        if (unmatched47) {
          if (_source47.is_Class) {
            DAST._IClass _1069_c = _source47.dtor_Class_a0;
            unmatched47 = false;
            Dafny.ISequence<RAST._IModDecl> _out17;
            _out17 = (this).GenClass(_1069_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1069_c).dtor_name)));
            _1066_generated = _out17;
          }
        }
        if (unmatched47) {
          if (_source47.is_Trait) {
            DAST._ITrait _1070_t = _source47.dtor_Trait_a0;
            unmatched47 = false;
            Dafny.ISequence<Dafny.Rune> _1071_tt;
            Dafny.ISequence<Dafny.Rune> _out18;
            _out18 = (this).GenTrait(_1070_t, containingPath);
            _1071_tt = _out18;
            _1066_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_RawDecl(_1071_tt));
          }
        }
        if (unmatched47) {
          if (_source47.is_Newtype) {
            DAST._INewtype _1072_n = _source47.dtor_Newtype_a0;
            unmatched47 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenNewtype(_1072_n);
            _1066_generated = _out19;
          }
        }
        if (unmatched47) {
          if (_source47.is_SynonymType) {
            DAST._ISynonymType _1073_s = _source47.dtor_SynonymType_a0;
            unmatched47 = false;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenSynonymType(_1073_s);
            _1066_generated = _out20;
          }
        }
        if (unmatched47) {
          DAST._IDatatype _1074_d = _source47.dtor_Datatype_a0;
          unmatched47 = false;
          Dafny.ISequence<RAST._IModDecl> _out21;
          _out21 = (this).GenDatatype(_1074_d);
          _1066_generated = _out21;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1066_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1075_genTpConstraint;
      _1075_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1075_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1075_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1075_genTpConstraint);
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
        for (BigInteger _1076_tpI = BigInteger.Zero; _1076_tpI < _hi6; _1076_tpI++) {
          DAST._ITypeArgDecl _1077_tp;
          _1077_tp = (@params).Select(_1076_tpI);
          DAST._IType _1078_typeArg;
          RAST._ITypeParamDecl _1079_typeParam;
          DAST._IType _out22;
          RAST._ITypeParamDecl _out23;
          (this).GenTypeParam(_1077_tp, out _out22, out _out23);
          _1078_typeArg = _out22;
          _1079_typeParam = _out23;
          RAST._IType _1080_rType;
          RAST._IType _out24;
          _out24 = (this).GenType(_1078_typeArg, false, false);
          _1080_rType = _out24;
          typeParamsSet = Dafny.Set<DAST._IType>.Union(typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1078_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1080_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1079_typeParam));
        }
      }
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1081_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1082_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1083_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1084_whereConstraints;
      Dafny.ISet<DAST._IType> _out25;
      Dafny.ISequence<RAST._IType> _out26;
      Dafny.ISequence<RAST._ITypeParamDecl> _out27;
      Dafny.ISequence<Dafny.Rune> _out28;
      (this).GenTypeParameters((c).dtor_typeParams, out _out25, out _out26, out _out27, out _out28);
      _1081_typeParamsSet = _out25;
      _1082_rTypeParams = _out26;
      _1083_rTypeParamsDecls = _out27;
      _1084_whereConstraints = _out28;
      Dafny.ISequence<Dafny.Rune> _1085_constrainedTypeParams;
      _1085_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1083_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1086_fields;
      _1086_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1087_fieldInits;
      _1087_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1088_fieldI = BigInteger.Zero; _1088_fieldI < _hi7; _1088_fieldI++) {
        DAST._IField _1089_field;
        _1089_field = ((c).dtor_fields).Select(_1088_fieldI);
        RAST._IType _1090_fieldType;
        RAST._IType _out29;
        _out29 = (this).GenType(((_1089_field).dtor_formal).dtor_typ, false, false);
        _1090_fieldType = _out29;
        Dafny.ISequence<Dafny.Rune> _1091_fieldRustName;
        _1091_fieldRustName = DCOMP.__default.escapeName(((_1089_field).dtor_formal).dtor_name);
        _1086_fields = Dafny.Sequence<RAST._IField>.Concat(_1086_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1091_fieldRustName, _1090_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source48 = (_1089_field).dtor_defaultValue;
        bool unmatched48 = true;
        if (unmatched48) {
          if (_source48.is_Some) {
            DAST._IExpression _1092_e = _source48.dtor_value;
            unmatched48 = false;
            {
              RAST._IExpr _1093_expr;
              DCOMP._IOwnership _1094___v44;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1095___v45;
              RAST._IExpr _out30;
              DCOMP._IOwnership _out31;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
              (this).GenExpr(_1092_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
              _1093_expr = _out30;
              _1094___v44 = _out31;
              _1095___v45 = _out32;
              _1087_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1087_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1091_fieldRustName, _1093_expr)));
            }
          }
        }
        if (unmatched48) {
          unmatched48 = false;
          {
            RAST._IExpr _1096_default;
            _1096_default = RAST.__default.std__Default__default;
            if ((_1090_fieldType).IsObjectOrPointer()) {
              _1096_default = (_1090_fieldType).ToNullExpr();
            }
            _1087_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1087_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1091_fieldRustName, _1096_default)));
          }
        }
      }
      BigInteger _hi8 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1097_typeParamI = BigInteger.Zero; _1097_typeParamI < _hi8; _1097_typeParamI++) {
        DAST._IType _1098_typeArg;
        RAST._ITypeParamDecl _1099_typeParam;
        DAST._IType _out33;
        RAST._ITypeParamDecl _out34;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1097_typeParamI), out _out33, out _out34);
        _1098_typeArg = _out33;
        _1099_typeParam = _out34;
        RAST._IType _1100_rTypeArg;
        RAST._IType _out35;
        _out35 = (this).GenType(_1098_typeArg, false, false);
        _1100_rTypeArg = _out35;
        _1086_fields = Dafny.Sequence<RAST._IField>.Concat(_1086_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1097_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1100_rTypeArg))))));
        _1087_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1087_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1097_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      Dafny.ISequence<Dafny.Rune> _1101_datatypeName;
      _1101_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IStruct _1102_struct;
      _1102_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1101_datatypeName, _1083_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1086_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1102_struct));
      DAST._IType _1103_underlyingDatatype;
      _1103_underlyingDatatype = DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(path, (c).dtor_attributes)));
      Dafny.ISequence<RAST._IImplMember> _1104_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1105_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out36;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out37;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_AllocatedDatatype(DAST.DatatypeType.create(path, (c).dtor_attributes))), _1081_typeParamsSet, out _out36, out _out37);
      _1104_implBodyRaw = _out36;
      _1105_traitBodies = _out37;
      Dafny.ISequence<RAST._IImplMember> _1106_implBody;
      _1106_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.Type.create_SelfOwned())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel((this).allocate)).ApplyType1(RAST.Type.create_SelfOwned())).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))))), _1104_implBodyRaw);
      RAST._IImpl _1107_i;
      _1107_i = RAST.Impl.create_Impl(_1083_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1101_datatypeName), _1082_rTypeParams), _1084_whereConstraints, _1106_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1107_i)));
      if ((new BigInteger(((c).dtor_superClasses).Count)).Sign == 1) {
        BigInteger _1108_i;
        _1108_i = BigInteger.Zero;
        while ((_1108_i) < (new BigInteger(((c).dtor_superClasses).Count))) {
          DAST._IType _1109_superClass;
          _1109_superClass = ((c).dtor_superClasses).Select(_1108_i);
          DAST._IType _source49 = _1109_superClass;
          bool unmatched49 = true;
          if (unmatched49) {
            if (_source49.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1110_traitPath = _source49.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _1111_typeArgs = _source49.dtor_typeArgs;
              DAST._IResolvedType resolved0 = _source49.dtor_resolved;
              if (resolved0.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1112___v46 = resolved0.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1113___v47 = resolved0.dtor_attributes;
                unmatched49 = false;
                {
                  RAST._IType _1114_pathStr;
                  RAST._IType _out38;
                  _out38 = DCOMP.COMP.GenPath(_1110_traitPath);
                  _1114_pathStr = _out38;
                  Dafny.ISequence<RAST._IType> _1115_typeArgs;
                  Dafny.ISequence<RAST._IType> _out39;
                  _out39 = (this).GenTypeArgs(_1111_typeArgs, false, false);
                  _1115_typeArgs = _out39;
                  Dafny.ISequence<RAST._IImplMember> _1116_body;
                  _1116_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((_1105_traitBodies).Contains(_1110_traitPath)) {
                    _1116_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1105_traitBodies,_1110_traitPath);
                  }
                  RAST._IType _1117_genSelfPath;
                  RAST._IType _out40;
                  _out40 = DCOMP.COMP.GenPath(path);
                  _1117_genSelfPath = _out40;
                  RAST._IModDecl _1118_x;
                  _1118_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1083_rTypeParamsDecls, RAST.Type.create_TypeApp(_1114_pathStr, _1115_typeArgs), RAST.Type.create_TypeApp(_1117_genSelfPath, _1082_rTypeParams), _1084_whereConstraints, _1116_body));
                  s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1118_x));
                }
              }
            }
          }
          if (unmatched49) {
            DAST._IType _1119___v48 = _source49;
            unmatched49 = false;
          }
          _1108_i = (_1108_i) + (BigInteger.One);
        }
      }
      return s;
    }
    public Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _1120_typeParamsSet;
      _1120_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1121_typeParamDecls;
      _1121_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1122_typeParams;
      _1122_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1123_tpI;
      _1123_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        while ((_1123_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._ITypeArgDecl _1124_tp;
          _1124_tp = ((t).dtor_typeParams).Select(_1123_tpI);
          DAST._IType _1125_typeArg;
          RAST._ITypeParamDecl _1126_typeParamDecl;
          DAST._IType _out41;
          RAST._ITypeParamDecl _out42;
          (this).GenTypeParam(_1124_tp, out _out41, out _out42);
          _1125_typeArg = _out41;
          _1126_typeParamDecl = _out42;
          _1120_typeParamsSet = Dafny.Set<DAST._IType>.Union(_1120_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1125_typeArg));
          _1121_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1121_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1126_typeParamDecl));
          RAST._IType _1127_typeParam;
          RAST._IType _out43;
          _out43 = (this).GenType(_1125_typeArg, false, false);
          _1127_typeParam = _out43;
          _1122_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1122_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1127_typeParam));
          _1123_tpI = (_1123_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1128_fullPath;
      _1128_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1129_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1130___v49;
      Dafny.ISequence<RAST._IImplMember> _out44;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out45;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_1128_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_1128_fullPath, (t).dtor_attributes)), _1120_typeParamsSet, out _out44, out _out45);
      _1129_implBody = _out44;
      _1130___v49 = _out45;
      s = (RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1121_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1122_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1129_implBody)))._ToString(DCOMP.__default.IND);
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1131_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1132_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1133_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1134_whereConstraints;
      Dafny.ISet<DAST._IType> _out46;
      Dafny.ISequence<RAST._IType> _out47;
      Dafny.ISequence<RAST._ITypeParamDecl> _out48;
      Dafny.ISequence<Dafny.Rune> _out49;
      (this).GenTypeParameters((c).dtor_typeParams, out _out46, out _out47, out _out48, out _out49);
      _1131_typeParamsSet = _out46;
      _1132_rTypeParams = _out47;
      _1133_rTypeParamsDecls = _out48;
      _1134_whereConstraints = _out49;
      Dafny.ISequence<Dafny.Rune> _1135_constrainedTypeParams;
      _1135_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1133_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1136_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source50 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      bool unmatched50 = true;
      if (unmatched50) {
        if (_source50.is_Some) {
          RAST._IType _1137_v = _source50.dtor_value;
          unmatched50 = false;
          _1136_underlyingType = _1137_v;
        }
      }
      if (unmatched50) {
        unmatched50 = false;
        RAST._IType _out50;
        _out50 = (this).GenType((c).dtor_base, false, false);
        _1136_underlyingType = _out50;
      }
      DAST._IType _1138_resultingType;
      _1138_resultingType = DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Newtype((c).dtor_base, (c).dtor_range, false, (c).dtor_attributes));
      Dafny.ISequence<Dafny.Rune> _1139_newtypeName;
      _1139_newtypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1139_newtypeName, _1133_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1136_underlyingType))))));
      RAST._IExpr _1140_fnBody;
      _1140_fnBody = RAST.Expr.create_Identifier(_1139_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source51 = (c).dtor_witnessExpr;
      bool unmatched51 = true;
      if (unmatched51) {
        if (_source51.is_Some) {
          DAST._IExpression _1141_e = _source51.dtor_value;
          unmatched51 = false;
          {
            DAST._IExpression _1142_e;
            _1142_e = ((object.Equals((c).dtor_base, _1138_resultingType)) ? (_1141_e) : (DAST.Expression.create_Convert(_1141_e, (c).dtor_base, _1138_resultingType)));
            RAST._IExpr _1143_eStr;
            DCOMP._IOwnership _1144___v50;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1145___v51;
            RAST._IExpr _out51;
            DCOMP._IOwnership _out52;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out53;
            (this).GenExpr(_1142_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out51, out _out52, out _out53);
            _1143_eStr = _out51;
            _1144___v50 = _out52;
            _1145___v51 = _out53;
            _1140_fnBody = (_1140_fnBody).Apply1(_1143_eStr);
          }
        }
      }
      if (unmatched51) {
        unmatched51 = false;
        {
          _1140_fnBody = (_1140_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1146_body;
      _1146_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1140_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source52 = (c).dtor_constraint;
      bool unmatched52 = true;
      if (unmatched52) {
        if (_source52.is_None) {
          unmatched52 = false;
        }
      }
      if (unmatched52) {
        DAST._INewtypeConstraint value8 = _source52.dtor_value;
        DAST._IFormal _1147_formal = value8.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _1148_constraintStmts = value8.dtor_constraintStmts;
        unmatched52 = false;
        RAST._IExpr _1149_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1150___v52;
        DCOMP._IEnvironment _1151_newEnv;
        RAST._IExpr _out54;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out55;
        DCOMP._IEnvironment _out56;
        (this).GenStmts(_1148_constraintStmts, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), false, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out54, out _out55, out _out56);
        _1149_rStmts = _out54;
        _1150___v52 = _out55;
        _1151_newEnv = _out56;
        Dafny.ISequence<RAST._IFormal> _1152_rFormals;
        Dafny.ISequence<RAST._IFormal> _out57;
        _out57 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_1147_formal));
        _1152_rFormals = _out57;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1133_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1139_newtypeName), _1132_rTypeParams), _1134_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _1152_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1149_rStmts))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1133_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1139_newtypeName), _1132_rTypeParams), _1134_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1146_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1133_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1139_newtypeName), _1132_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1133_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1139_newtypeName), _1132_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1136_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1153_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1154_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1155_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1156_whereConstraints;
      Dafny.ISet<DAST._IType> _out58;
      Dafny.ISequence<RAST._IType> _out59;
      Dafny.ISequence<RAST._ITypeParamDecl> _out60;
      Dafny.ISequence<Dafny.Rune> _out61;
      (this).GenTypeParameters((c).dtor_typeParams, out _out58, out _out59, out _out60, out _out61);
      _1153_typeParamsSet = _out58;
      _1154_rTypeParams = _out59;
      _1155_rTypeParamsDecls = _out60;
      _1156_whereConstraints = _out61;
      Dafny.ISequence<Dafny.Rune> _1157_constrainedTypeParams;
      _1157_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1155_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<Dafny.Rune> _1158_synonymTypeName;
      _1158_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _1159_resultingType;
      RAST._IType _out62;
      _out62 = (this).GenType((c).dtor_base, false, false);
      _1159_resultingType = _out62;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1158_synonymTypeName, _1155_rTypeParamsDecls, _1159_resultingType)));
      Std.Wrappers._IOption<DAST._IExpression> _source53 = (c).dtor_witnessExpr;
      bool unmatched53 = true;
      if (unmatched53) {
        if (_source53.is_Some) {
          DAST._IExpression _1160_e = _source53.dtor_value;
          unmatched53 = false;
          {
            RAST._IExpr _1161_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1162___v53;
            DCOMP._IEnvironment _1163_newEnv;
            RAST._IExpr _out63;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out64;
            DCOMP._IEnvironment _out65;
            (this).GenStmts((c).dtor_witnessStmts, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), false, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out63, out _out64, out _out65);
            _1161_rStmts = _out63;
            _1162___v53 = _out64;
            _1163_newEnv = _out65;
            RAST._IExpr _1164_rExpr;
            DCOMP._IOwnership _1165___v54;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1166___v55;
            RAST._IExpr _out66;
            DCOMP._IOwnership _out67;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out68;
            (this).GenExpr(_1160_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), _1163_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out66, out _out67, out _out68);
            _1164_rExpr = _out66;
            _1165___v54 = _out67;
            _1166___v55 = _out68;
            Dafny.ISequence<Dafny.Rune> _1167_constantName;
            _1167_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_1167_constantName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1159_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_1161_rStmts).Then(_1164_rExpr)))))));
          }
        }
      }
      if (unmatched53) {
        unmatched53 = false;
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1168_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1169_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1170_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1171_whereConstraints;
      Dafny.ISet<DAST._IType> _out69;
      Dafny.ISequence<RAST._IType> _out70;
      Dafny.ISequence<RAST._ITypeParamDecl> _out71;
      Dafny.ISequence<Dafny.Rune> _out72;
      (this).GenTypeParameters((c).dtor_typeParams, out _out69, out _out70, out _out71, out _out72);
      _1168_typeParamsSet = _out69;
      _1169_rTypeParams = _out70;
      _1170_rTypeParamsDecls = _out71;
      _1171_whereConstraints = _out72;
      Dafny.ISequence<Dafny.Rune> _1172_datatypeName;
      _1172_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1173_ctors;
      _1173_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      BigInteger _hi9 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1174_i = BigInteger.Zero; _1174_i < _hi9; _1174_i++) {
        DAST._IDatatypeCtor _1175_ctor;
        _1175_ctor = ((c).dtor_ctors).Select(_1174_i);
        Dafny.ISequence<RAST._IField> _1176_ctorArgs;
        _1176_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1177_isNumeric;
        _1177_isNumeric = false;
        BigInteger _hi10 = new BigInteger(((_1175_ctor).dtor_args).Count);
        for (BigInteger _1178_j = BigInteger.Zero; _1178_j < _hi10; _1178_j++) {
          DAST._IDatatypeDtor _1179_dtor;
          _1179_dtor = ((_1175_ctor).dtor_args).Select(_1178_j);
          RAST._IType _1180_formalType;
          RAST._IType _out73;
          _out73 = (this).GenType(((_1179_dtor).dtor_formal).dtor_typ, false, false);
          _1180_formalType = _out73;
          Dafny.ISequence<Dafny.Rune> _1181_formalName;
          _1181_formalName = DCOMP.__default.escapeName(((_1179_dtor).dtor_formal).dtor_name);
          if (((_1178_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1181_formalName))) {
            _1177_isNumeric = true;
          }
          if ((((_1178_j).Sign != 0) && (_1177_isNumeric)) && (!(Std.Strings.__default.OfNat(_1178_j)).Equals(_1181_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1181_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1178_j)));
            _1177_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1176_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1176_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1181_formalName, RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1180_formalType))))));
          } else {
            _1176_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1176_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1181_formalName, _1180_formalType))));
          }
        }
        RAST._IFields _1182_namedFields;
        _1182_namedFields = RAST.Fields.create_NamedFields(_1176_ctorArgs);
        if (_1177_isNumeric) {
          _1182_namedFields = (_1182_namedFields).ToNamelessFields();
        }
        _1173_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1173_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1175_ctor).dtor_name), _1182_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1183_selfPath;
      _1183_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1184_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1185_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out74;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out75;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(_1183_selfPath, (c).dtor_attributes))), _1168_typeParamsSet, out _out74, out _out75);
      _1184_implBodyRaw = _out74;
      _1185_traitBodies = _out75;
      Dafny.ISequence<RAST._IImplMember> _1186_implBody;
      _1186_implBody = _1184_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1187_emittedFields;
      _1187_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi11 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1188_i = BigInteger.Zero; _1188_i < _hi11; _1188_i++) {
        DAST._IDatatypeCtor _1189_ctor;
        _1189_ctor = ((c).dtor_ctors).Select(_1188_i);
        BigInteger _hi12 = new BigInteger(((_1189_ctor).dtor_args).Count);
        for (BigInteger _1190_j = BigInteger.Zero; _1190_j < _hi12; _1190_j++) {
          DAST._IDatatypeDtor _1191_dtor;
          _1191_dtor = ((_1189_ctor).dtor_args).Select(_1190_j);
          Dafny.ISequence<Dafny.Rune> _1192_callName;
          _1192_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1191_dtor).dtor_callName, DCOMP.__default.escapeName(((_1191_dtor).dtor_formal).dtor_name));
          if (!((_1187_emittedFields).Contains(_1192_callName))) {
            _1187_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1187_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1192_callName));
            RAST._IType _1193_formalType;
            RAST._IType _out76;
            _out76 = (this).GenType(((_1191_dtor).dtor_formal).dtor_typ, false, false);
            _1193_formalType = _out76;
            Dafny.ISequence<RAST._IMatchCase> _1194_cases;
            _1194_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1195_k = BigInteger.Zero; _1195_k < _hi13; _1195_k++) {
              DAST._IDatatypeCtor _1196_ctor2;
              _1196_ctor2 = ((c).dtor_ctors).Select(_1195_k);
              Dafny.ISequence<Dafny.Rune> _1197_pattern;
              _1197_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1172_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1196_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1198_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1199_hasMatchingField;
              _1199_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1200_patternInner;
              _1200_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1201_isNumeric;
              _1201_isNumeric = false;
              BigInteger _hi14 = new BigInteger(((_1196_ctor2).dtor_args).Count);
              for (BigInteger _1202_l = BigInteger.Zero; _1202_l < _hi14; _1202_l++) {
                DAST._IDatatypeDtor _1203_dtor2;
                _1203_dtor2 = ((_1196_ctor2).dtor_args).Select(_1202_l);
                Dafny.ISequence<Dafny.Rune> _1204_patternName;
                _1204_patternName = DCOMP.__default.escapeName(((_1203_dtor2).dtor_formal).dtor_name);
                if (((_1202_l).Sign == 0) && ((_1204_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1201_isNumeric = true;
                }
                if (_1201_isNumeric) {
                  _1204_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1203_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1202_l)));
                }
                if (object.Equals(((_1191_dtor).dtor_formal).dtor_name, ((_1203_dtor2).dtor_formal).dtor_name)) {
                  _1199_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1204_patternName);
                }
                _1200_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1200_patternInner, _1204_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1201_isNumeric) {
                _1197_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1197_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1200_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1197_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1197_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1200_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1199_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1198_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1199_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1198_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1199_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1198_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _1205_ctorMatch;
              _1205_ctorMatch = RAST.MatchCase.create(_1197_pattern, RAST.Expr.create_RawExpr(_1198_rhs));
              _1194_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1194_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1205_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1194_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1194_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1172_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _1206_methodBody;
            _1206_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1194_cases);
            _1186_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1186_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1192_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1193_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1206_methodBody)))));
          }
        }
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1207_types;
        _1207_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi15 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1208_typeI = BigInteger.Zero; _1208_typeI < _hi15; _1208_typeI++) {
          DAST._IType _1209_typeArg;
          RAST._ITypeParamDecl _1210_rTypeParamDecl;
          DAST._IType _out77;
          RAST._ITypeParamDecl _out78;
          (this).GenTypeParam(((c).dtor_typeParams).Select(_1208_typeI), out _out77, out _out78);
          _1209_typeArg = _out77;
          _1210_rTypeParamDecl = _out78;
          RAST._IType _1211_rTypeArg;
          RAST._IType _out79;
          _out79 = (this).GenType(_1209_typeArg, false, false);
          _1211_rTypeArg = _out79;
          _1207_types = Dafny.Sequence<RAST._IType>.Concat(_1207_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1211_rTypeArg))));
        }
        _1173_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1173_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1212_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1212_tpe);
})), _1207_types)))));
      }
      Dafny.ISequence<RAST._IModDecl> _1213_enumBody;
      _1213_enumBody = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]")), _1172_datatypeName, _1170_rTypeParamsDecls, _1173_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1170_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1172_datatypeName), _1169_rTypeParams), _1171_whereConstraints, _1186_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1214_printImplBodyCases;
      _1214_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1215_hashImplBodyCases;
      _1215_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1216_i = BigInteger.Zero; _1216_i < _hi16; _1216_i++) {
        DAST._IDatatypeCtor _1217_ctor;
        _1217_ctor = ((c).dtor_ctors).Select(_1216_i);
        Dafny.ISequence<Dafny.Rune> _1218_ctorMatch;
        _1218_ctorMatch = DCOMP.__default.escapeName((_1217_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1219_modulePrefix;
        _1219_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1220_ctorName;
        _1220_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1219_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1217_ctor).dtor_name));
        if (((new BigInteger((_1220_ctorName).Count)) >= (new BigInteger(13))) && (((_1220_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1220_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1221_printRhs;
        _1221_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1220_ctorName), (((_1217_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1222_hashRhs;
        _1222_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        bool _1223_isNumeric;
        _1223_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1224_ctorMatchInner;
        _1224_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi17 = new BigInteger(((_1217_ctor).dtor_args).Count);
        for (BigInteger _1225_j = BigInteger.Zero; _1225_j < _hi17; _1225_j++) {
          DAST._IDatatypeDtor _1226_dtor;
          _1226_dtor = ((_1217_ctor).dtor_args).Select(_1225_j);
          Dafny.ISequence<Dafny.Rune> _1227_patternName;
          _1227_patternName = DCOMP.__default.escapeName(((_1226_dtor).dtor_formal).dtor_name);
          if (((_1225_j).Sign == 0) && ((_1227_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1223_isNumeric = true;
          }
          if (_1223_isNumeric) {
            _1227_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1226_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1225_j)));
          }
          _1222_hashRhs = (_1222_hashRhs).Then(((RAST.Expr.create_Identifier(_1227_patternName)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))));
          _1224_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1224_ctorMatchInner, _1227_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1225_j).Sign == 1) {
            _1221_printRhs = (_1221_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1221_printRhs = (_1221_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1227_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))));
        }
        if (_1223_isNumeric) {
          _1218_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1218_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1224_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1218_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1218_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1224_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1217_ctor).dtor_hasAnyArgs) {
          _1221_printRhs = (_1221_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1221_printRhs = (_1221_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1214_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1214_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1172_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1218_ctorMatch), RAST.Expr.create_Block(_1221_printRhs))));
        _1215_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1215_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1172_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1218_ctorMatch), RAST.Expr.create_Block(_1222_hashRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _1214_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1214_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1172_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
        _1215_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1215_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1172_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1228_defaultConstrainedTypeParams;
      _1228_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1170_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1229_rTypeParamsDeclsWithEq;
      _1229_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1170_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1230_rTypeParamsDeclsWithHash;
      _1230_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1170_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1231_printImplBody;
      _1231_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1214_printImplBodyCases);
      RAST._IExpr _1232_hashImplBody;
      _1232_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1215_hashImplBodyCases);
      Dafny.ISequence<RAST._IModDecl> _1233_printImpl;
      _1233_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1170_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1172_datatypeName), _1169_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1170_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1172_datatypeName), _1169_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1231_printImplBody)))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1229_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1172_datatypeName), _1169_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements())), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1230_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1172_datatypeName), _1169_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1232_hashImplBody)))))));
      Dafny.ISequence<RAST._IModDecl> _1234_defaultImpl;
      _1234_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      Dafny.ISequence<RAST._IModDecl> _1235_asRefImpl;
      _1235_asRefImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1236_structName;
        _1236_structName = (RAST.Expr.create_Identifier(_1172_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1237_structAssignments;
        _1237_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi18 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1238_i = BigInteger.Zero; _1238_i < _hi18; _1238_i++) {
          DAST._IDatatypeDtor _1239_dtor;
          _1239_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1238_i);
          _1237_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1237_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1239_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1240_defaultConstrainedTypeParams;
        _1240_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1170_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1241_fullType;
        _1241_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1172_datatypeName), _1169_rTypeParams);
        _1234_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1240_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1241_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1241_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1236_structName, _1237_structAssignments))))))));
        _1235_asRefImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1170_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_1241_fullType), RAST.Type.create_Borrowed(_1241_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self)))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(_1213_enumBody, _1233_printImpl), _1234_defaultImpl), _1235_asRefImpl);
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
        for (BigInteger _1242_i = BigInteger.Zero; _1242_i < _hi19; _1242_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1242_i))));
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
        for (BigInteger _1243_i = BigInteger.Zero; _1243_i < _hi20; _1243_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1243_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding, bool inFn)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger((args).Count)).Sign == 1) {
        BigInteger _1244_i;
        _1244_i = BigInteger.Zero;
        while ((_1244_i) < (new BigInteger((args).Count))) {
          RAST._IType _1245_genTp;
          RAST._IType _out80;
          _out80 = (this).GenType((args).Select(_1244_i), inBinding, inFn);
          _1245_genTp = _out80;
          s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1245_genTp));
          _1244_i = (_1244_i) + (BigInteger.One);
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
      DAST._IType _source54 = c;
      bool unmatched54 = true;
      if (unmatched54) {
        if (_source54.is_Path) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1246_p = _source54.dtor_Path_a0;
          Dafny.ISequence<DAST._IType> _1247_args = _source54.dtor_typeArgs;
          DAST._IResolvedType _1248_resolved = _source54.dtor_resolved;
          unmatched54 = false;
          {
            RAST._IType _1249_t;
            RAST._IType _out81;
            _out81 = DCOMP.COMP.GenPath(_1246_p);
            _1249_t = _out81;
            Dafny.ISequence<RAST._IType> _1250_typeArgs;
            Dafny.ISequence<RAST._IType> _out82;
            _out82 = (this).GenTypeArgs(_1247_args, inBinding, inFn);
            _1250_typeArgs = _out82;
            s = RAST.Type.create_TypeApp(_1249_t, _1250_typeArgs);
            DAST._IResolvedType _source55 = _1248_resolved;
            bool unmatched55 = true;
            if (unmatched55) {
              if (_source55.is_AllocatedDatatype) {
                DAST._IDatatypeType datatypeType0 = _source55.dtor_datatypeType;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1251___v56 = datatypeType0.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1252_attributes = datatypeType0.dtor_attributes;
                unmatched55 = false;
                {
                  s = (this).Object(s);
                }
              }
            }
            if (unmatched55) {
              if (_source55.is_Datatype) {
                DAST._IDatatypeType datatypeType1 = _source55.dtor_datatypeType;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1253___v57 = datatypeType1.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1254_attributes = datatypeType1.dtor_attributes;
                unmatched55 = false;
                {
                  if ((this).IsRcWrapped(_1254_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                  if ((this).IsRcWrapped(_1254_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched55) {
              if (_source55.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1255___v58 = _source55.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1256___v59 = _source55.dtor_attributes;
                unmatched55 = false;
                {
                  if ((_1246_p).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
                  }
                  s = (this).Object(RAST.Type.create_DynType(s));
                }
              }
            }
            if (unmatched55) {
              DAST._IType _1257_t = _source55.dtor_baseType;
              DAST._INewtypeRange _1258_range = _source55.dtor_range;
              bool _1259_erased = _source55.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1260_attributes = _source55.dtor_attributes;
              unmatched55 = false;
              {
                if (_1259_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source56 = DCOMP.COMP.NewtypeToRustType(_1257_t, _1258_range);
                  bool unmatched56 = true;
                  if (unmatched56) {
                    if (_source56.is_Some) {
                      RAST._IType _1261_v = _source56.dtor_value;
                      unmatched56 = false;
                      s = _1261_v;
                    }
                  }
                  if (unmatched56) {
                    unmatched56 = false;
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched54) {
        if (_source54.is_Nullable) {
          DAST._IType _1262_inner = _source54.dtor_Nullable_a0;
          unmatched54 = false;
          {
            RAST._IType _1263_innerExpr;
            RAST._IType _out83;
            _out83 = (this).GenType(_1262_inner, inBinding, inFn);
            _1263_innerExpr = _out83;
            s = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::option::Option")), Dafny.Sequence<RAST._IType>.FromElements(_1263_innerExpr));
          }
        }
      }
      if (unmatched54) {
        if (_source54.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1264_types = _source54.dtor_Tuple_a0;
          unmatched54 = false;
          {
            Dafny.ISequence<RAST._IType> _1265_args;
            _1265_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1266_i;
            _1266_i = BigInteger.Zero;
            while ((_1266_i) < (new BigInteger((_1264_types).Count))) {
              RAST._IType _1267_generated;
              RAST._IType _out84;
              _out84 = (this).GenType((_1264_types).Select(_1266_i), inBinding, inFn);
              _1267_generated = _out84;
              _1265_args = Dafny.Sequence<RAST._IType>.Concat(_1265_args, Dafny.Sequence<RAST._IType>.FromElements(_1267_generated));
              _1266_i = (_1266_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1264_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1265_args)) : (RAST.__default.SystemTupleType(_1265_args)));
          }
        }
      }
      if (unmatched54) {
        if (_source54.is_Array) {
          DAST._IType _1268_element = _source54.dtor_element;
          BigInteger _1269_dims = _source54.dtor_dims;
          unmatched54 = false;
          {
            if ((_1269_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1270_elem;
              RAST._IType _out85;
              _out85 = (this).GenType(_1268_element, inBinding, inFn);
              _1270_elem = _out85;
              if ((_1269_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1270_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1271_n;
                _1271_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1269_dims));
                s = ((RAST.__default.dafny__runtime__type).MSel(_1271_n)).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1270_elem));
                s = (this).Object(s);
              }
            }
          }
        }
      }
      if (unmatched54) {
        if (_source54.is_Seq) {
          DAST._IType _1272_element = _source54.dtor_element;
          unmatched54 = false;
          {
            RAST._IType _1273_elem;
            RAST._IType _out86;
            _out86 = (this).GenType(_1272_element, inBinding, inFn);
            _1273_elem = _out86;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1273_elem));
          }
        }
      }
      if (unmatched54) {
        if (_source54.is_Set) {
          DAST._IType _1274_element = _source54.dtor_element;
          unmatched54 = false;
          {
            RAST._IType _1275_elem;
            RAST._IType _out87;
            _out87 = (this).GenType(_1274_element, inBinding, inFn);
            _1275_elem = _out87;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1275_elem));
          }
        }
      }
      if (unmatched54) {
        if (_source54.is_Multiset) {
          DAST._IType _1276_element = _source54.dtor_element;
          unmatched54 = false;
          {
            RAST._IType _1277_elem;
            RAST._IType _out88;
            _out88 = (this).GenType(_1276_element, inBinding, inFn);
            _1277_elem = _out88;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1277_elem));
          }
        }
      }
      if (unmatched54) {
        if (_source54.is_Map) {
          DAST._IType _1278_key = _source54.dtor_key;
          DAST._IType _1279_value = _source54.dtor_value;
          unmatched54 = false;
          {
            RAST._IType _1280_keyType;
            RAST._IType _out89;
            _out89 = (this).GenType(_1278_key, inBinding, inFn);
            _1280_keyType = _out89;
            RAST._IType _1281_valueType;
            RAST._IType _out90;
            _out90 = (this).GenType(_1279_value, inBinding, inFn);
            _1281_valueType = _out90;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1280_keyType, _1281_valueType));
          }
        }
      }
      if (unmatched54) {
        if (_source54.is_MapBuilder) {
          DAST._IType _1282_key = _source54.dtor_key;
          DAST._IType _1283_value = _source54.dtor_value;
          unmatched54 = false;
          {
            RAST._IType _1284_keyType;
            RAST._IType _out91;
            _out91 = (this).GenType(_1282_key, inBinding, inFn);
            _1284_keyType = _out91;
            RAST._IType _1285_valueType;
            RAST._IType _out92;
            _out92 = (this).GenType(_1283_value, inBinding, inFn);
            _1285_valueType = _out92;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1284_keyType, _1285_valueType));
          }
        }
      }
      if (unmatched54) {
        if (_source54.is_SetBuilder) {
          DAST._IType _1286_elem = _source54.dtor_element;
          unmatched54 = false;
          {
            RAST._IType _1287_elemType;
            RAST._IType _out93;
            _out93 = (this).GenType(_1286_elem, inBinding, inFn);
            _1287_elemType = _out93;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1287_elemType));
          }
        }
      }
      if (unmatched54) {
        if (_source54.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1288_args = _source54.dtor_args;
          DAST._IType _1289_result = _source54.dtor_result;
          unmatched54 = false;
          {
            Dafny.ISequence<RAST._IType> _1290_argTypes;
            _1290_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1291_i;
            _1291_i = BigInteger.Zero;
            while ((_1291_i) < (new BigInteger((_1288_args).Count))) {
              RAST._IType _1292_generated;
              RAST._IType _out94;
              _out94 = (this).GenType((_1288_args).Select(_1291_i), inBinding, true);
              _1292_generated = _out94;
              _1290_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1290_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1292_generated)));
              _1291_i = (_1291_i) + (BigInteger.One);
            }
            RAST._IType _1293_resultType;
            RAST._IType _out95;
            _out95 = (this).GenType(_1289_result, inBinding, (inFn) || (inBinding));
            _1293_resultType = _out95;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1290_argTypes, _1293_resultType)));
          }
        }
      }
      if (unmatched54) {
        if (_source54.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h110 = _source54.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1294_name = _h110;
          unmatched54 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1294_name));
        }
      }
      if (unmatched54) {
        if (_source54.is_Primitive) {
          DAST._IPrimitive _1295_p = _source54.dtor_Primitive_a0;
          unmatched54 = false;
          {
            DAST._IPrimitive _source57 = _1295_p;
            bool unmatched57 = true;
            if (unmatched57) {
              if (_source57.is_Int) {
                unmatched57 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
              }
            }
            if (unmatched57) {
              if (_source57.is_Real) {
                unmatched57 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
              }
            }
            if (unmatched57) {
              if (_source57.is_String) {
                unmatched57 = false;
                s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
              }
            }
            if (unmatched57) {
              if (_source57.is_Bool) {
                unmatched57 = false;
                s = RAST.Type.create_Bool();
              }
            }
            if (unmatched57) {
              unmatched57 = false;
              s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
            }
          }
        }
      }
      if (unmatched54) {
        Dafny.ISequence<Dafny.Rune> _1296_v = _source54.dtor_Passthrough_a0;
        unmatched54 = false;
        s = RAST.__default.RawType(_1296_v);
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
      for (BigInteger _1297_i = BigInteger.Zero; _1297_i < _hi21; _1297_i++) {
        DAST._IMethod _source58 = (body).Select(_1297_i);
        bool unmatched58 = true;
        if (unmatched58) {
          DAST._IMethod _1298_m = _source58;
          unmatched58 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source59 = (_1298_m).dtor_overridingPath;
            bool unmatched59 = true;
            if (unmatched59) {
              if (_source59.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1299_p = _source59.dtor_value;
                unmatched59 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1300_existing;
                  _1300_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1299_p)) {
                    _1300_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1299_p);
                  }
                  RAST._IImplMember _1301_genMethod;
                  RAST._IImplMember _out96;
                  _out96 = (this).GenMethod(_1298_m, true, enclosingType, enclosingTypeParams);
                  _1301_genMethod = _out96;
                  _1300_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1300_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1301_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1299_p, _1300_existing)));
                }
              }
            }
            if (unmatched59) {
              unmatched59 = false;
              {
                RAST._IImplMember _1302_generated;
                RAST._IImplMember _out97;
                _out97 = (this).GenMethod(_1298_m, forTrait, enclosingType, enclosingTypeParams);
                _1302_generated = _out97;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1302_generated));
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
      for (BigInteger _1303_i = BigInteger.Zero; _1303_i < _hi22; _1303_i++) {
        DAST._IFormal _1304_param;
        _1304_param = (@params).Select(_1303_i);
        RAST._IType _1305_paramType;
        RAST._IType _out98;
        _out98 = (this).GenType((_1304_param).dtor_typ, false, false);
        _1305_paramType = _out98;
        if ((!((_1305_paramType).CanReadWithoutClone())) && (!((_1304_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1305_paramType = RAST.Type.create_Borrowed(_1305_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_1304_param).dtor_name), _1305_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1306_params;
      Dafny.ISequence<RAST._IFormal> _out99;
      _out99 = (this).GenParams((m).dtor_params);
      _1306_params = _out99;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1307_paramNames;
      _1307_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1308_paramTypes;
      _1308_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi23 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1309_paramI = BigInteger.Zero; _1309_paramI < _hi23; _1309_paramI++) {
        DAST._IFormal _1310_dafny__formal;
        _1310_dafny__formal = ((m).dtor_params).Select(_1309_paramI);
        RAST._IFormal _1311_formal;
        _1311_formal = (_1306_params).Select(_1309_paramI);
        Dafny.ISequence<Dafny.Rune> _1312_name;
        _1312_name = (_1311_formal).dtor_name;
        _1307_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1307_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1312_name));
        _1308_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1308_paramTypes, _1312_name, (_1311_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1313_fnName;
      _1313_fnName = DCOMP.__default.escapeName((m).dtor_name);
      Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1314_selfIdentifier;
      _1314_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1315_selfId;
        _1315_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((_1313_fnName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_ctor"))) {
          _1315_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        if (forTrait) {
          RAST._IFormal _1316_selfFormal;
          _1316_selfFormal = (((m).dtor_wasFunction) ? (RAST.Formal.selfBorrowed) : (RAST.Formal.selfBorrowedMut));
          _1306_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1316_selfFormal), _1306_params);
        } else {
          RAST._IType _1317_tpe;
          RAST._IType _out100;
          _out100 = (this).GenType(enclosingType, false, false);
          _1317_tpe = _out100;
          if (((_1315_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) && ((_1317_tpe).IsObjectOrPointer())) {
            if ((m).dtor_wasFunction) {
              _1317_tpe = RAST.__default.SelfBorrowed;
            } else {
              _1317_tpe = RAST.__default.SelfBorrowedMut;
            }
          } else {
            if (!((_1317_tpe).CanReadWithoutClone())) {
              _1317_tpe = RAST.Type.create_Borrowed(_1317_tpe);
            }
          }
          _1306_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1315_selfId, _1317_tpe)), _1306_params);
        }
        _1314_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1315_selfId);
      }
      Dafny.ISequence<RAST._IType> _1318_retTypeArgs;
      _1318_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1319_typeI;
      _1319_typeI = BigInteger.Zero;
      while ((_1319_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1320_typeExpr;
        RAST._IType _out101;
        _out101 = (this).GenType(((m).dtor_outTypes).Select(_1319_typeI), false, false);
        _1320_typeExpr = _out101;
        _1318_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1318_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1320_typeExpr));
        _1319_typeI = (_1319_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1321_visibility;
      _1321_visibility = ((forTrait) ? (RAST.Visibility.create_PRIV()) : (RAST.Visibility.create_PUB()));
      Dafny.ISequence<DAST._ITypeArgDecl> _1322_typeParamsFiltered;
      _1322_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi24 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1323_typeParamI = BigInteger.Zero; _1323_typeParamI < _hi24; _1323_typeParamI++) {
        DAST._ITypeArgDecl _1324_typeParam;
        _1324_typeParam = ((m).dtor_typeParams).Select(_1323_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1324_typeParam).dtor_name)))) {
          _1322_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1322_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1324_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1325_typeParams;
      _1325_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1322_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi25 = new BigInteger((_1322_typeParamsFiltered).Count);
        for (BigInteger _1326_i = BigInteger.Zero; _1326_i < _hi25; _1326_i++) {
          DAST._IType _1327_typeArg;
          RAST._ITypeParamDecl _1328_rTypeParamDecl;
          DAST._IType _out102;
          RAST._ITypeParamDecl _out103;
          (this).GenTypeParam((_1322_typeParamsFiltered).Select(_1326_i), out _out102, out _out103);
          _1327_typeArg = _out102;
          _1328_rTypeParamDecl = _out103;
          var _pat_let_tv104 = _1328_rTypeParamDecl;
          _1328_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1328_rTypeParamDecl, _pat_let9_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let9_0, _1329_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Dafny.Sequence<RAST._IType>.Concat((_pat_let_tv104).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default")))), _pat_let10_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let10_0, _1330_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1329_dt__update__tmp_h0).dtor_content, _1330_dt__update_hconstraints_h0)))));
          _1325_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1325_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1328_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1331_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1332_env = DCOMP.Environment.Default();
      RAST._IExpr _1333_preBody;
      _1333_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1334_preAssignNames;
      _1334_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1335_preAssignTypes;
      _1335_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        RAST._IExpr _1336_earlyReturn;
        _1336_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source60 = (m).dtor_outVars;
        bool unmatched60 = true;
        if (unmatched60) {
          if (_source60.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1337_outVars = _source60.dtor_value;
            unmatched60 = false;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1336_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(Dafny.Sequence<RAST._IExpr>.FromElements())));
                BigInteger _hi26 = new BigInteger((_1337_outVars).Count);
                for (BigInteger _1338_outI = BigInteger.Zero; _1338_outI < _hi26; _1338_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1339_outVar;
                  _1339_outVar = (_1337_outVars).Select(_1338_outI);
                  Dafny.ISequence<Dafny.Rune> _1340_outName;
                  _1340_outName = DCOMP.__default.escapeName((_1339_outVar));
                  Dafny.ISequence<Dafny.Rune> _1341_tracker__name;
                  _1341_tracker__name = DCOMP.__default.AddAssignedPrefix(_1340_outName);
                  _1334_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1334_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1341_tracker__name));
                  _1335_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1335_preAssignTypes, _1341_tracker__name, RAST.Type.create_Bool());
                  _1333_preBody = (_1333_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1341_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<RAST._IExpr> _1342_tupleArgs;
                _1342_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
                BigInteger _hi27 = new BigInteger((_1337_outVars).Count);
                for (BigInteger _1343_outI = BigInteger.Zero; _1343_outI < _hi27; _1343_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1344_outVar;
                  _1344_outVar = (_1337_outVars).Select(_1343_outI);
                  RAST._IType _1345_outType;
                  RAST._IType _out104;
                  _out104 = (this).GenType(((m).dtor_outTypes).Select(_1343_outI), false, false);
                  _1345_outType = _out104;
                  Dafny.ISequence<Dafny.Rune> _1346_outName;
                  _1346_outName = DCOMP.__default.escapeName((_1344_outVar));
                  _1307_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1307_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1346_outName));
                  RAST._IType _1347_outMaybeType;
                  _1347_outMaybeType = (((_1345_outType).CanReadWithoutClone()) ? (_1345_outType) : (RAST.__default.MaybePlaceboType(_1345_outType)));
                  _1308_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1308_paramTypes, _1346_outName, _1347_outMaybeType);
                  RAST._IExpr _1348_outVarReturn;
                  DCOMP._IOwnership _1349___v60;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1350___v61;
                  RAST._IExpr _out105;
                  DCOMP._IOwnership _out106;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out107;
                  (this).GenExpr(DAST.Expression.create_Ident((_1344_outVar)), Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1346_outName), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>, RAST._IType>(_1346_outName, _1347_outMaybeType))), DCOMP.Ownership.create_OwnershipOwned(), out _out105, out _out106, out _out107);
                  _1348_outVarReturn = _out105;
                  _1349___v60 = _out106;
                  _1350___v61 = _out107;
                  _1342_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1342_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1348_outVarReturn));
                }
                if ((new BigInteger((_1342_tupleArgs).Count)) == (BigInteger.One)) {
                  _1336_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1342_tupleArgs).Select(BigInteger.Zero)));
                } else {
                  _1336_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1342_tupleArgs)));
                }
              }
            }
          }
        }
        if (unmatched60) {
          unmatched60 = false;
        }
        _1332_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1334_preAssignNames, _1307_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1335_preAssignTypes, _1308_paramTypes));
        RAST._IExpr _1351_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1352___v62;
        DCOMP._IEnvironment _1353___v63;
        RAST._IExpr _out108;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out109;
        DCOMP._IEnvironment _out110;
        (this).GenStmts((m).dtor_body, _1314_selfIdentifier, _1332_env, true, _1336_earlyReturn, out _out108, out _out109, out _out110);
        _1351_body = _out108;
        _1352___v62 = _out109;
        _1353___v63 = _out110;
        _1331_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1333_preBody).Then(_1351_body));
      } else {
        _1332_env = DCOMP.Environment.create(_1307_paramNames, _1308_paramTypes);
        _1331_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1321_visibility, RAST.Fn.create(_1313_fnName, _1325_typeParams, _1306_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1318_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1318_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1318_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1331_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1354_declarations;
      _1354_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1355_i;
      _1355_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1356_stmts;
      _1356_stmts = stmts;
      while ((_1355_i) < (new BigInteger((_1356_stmts).Count))) {
        DAST._IStatement _1357_stmt;
        _1357_stmt = (_1356_stmts).Select(_1355_i);
        DAST._IStatement _source61 = _1357_stmt;
        bool unmatched61 = true;
        if (unmatched61) {
          if (_source61.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1358_name = _source61.dtor_name;
            DAST._IType _1359_optType = _source61.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source61.dtor_maybeValue;
            if (maybeValue0.is_None) {
              unmatched61 = false;
              if (((_1355_i) + (BigInteger.One)) < (new BigInteger((_1356_stmts).Count))) {
                DAST._IStatement _source62 = (_1356_stmts).Select((_1355_i) + (BigInteger.One));
                bool unmatched62 = true;
                if (unmatched62) {
                  if (_source62.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source62.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> ident0 = lhs0.dtor_ident;
                      Dafny.ISequence<Dafny.Rune> _1360_name2 = ident0;
                      DAST._IExpression _1361_rhs = _source62.dtor_value;
                      unmatched62 = false;
                      if (object.Equals(_1360_name2, _1358_name)) {
                        _1356_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1356_stmts).Subsequence(BigInteger.Zero, _1355_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1358_name, _1359_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1361_rhs)))), (_1356_stmts).Drop((_1355_i) + (BigInteger.One)));
                        _1357_stmt = (_1356_stmts).Select(_1355_i);
                      }
                    }
                  }
                }
                if (unmatched62) {
                  DAST._IStatement _1362___v64 = _source62;
                  unmatched62 = false;
                }
              }
            }
          }
        }
        if (unmatched61) {
          DAST._IStatement _1363___v65 = _source61;
          unmatched61 = false;
        }
        RAST._IExpr _1364_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1365_recIdents;
        DCOMP._IEnvironment _1366_newEnv2;
        RAST._IExpr _out111;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out112;
        DCOMP._IEnvironment _out113;
        (this).GenStmt(_1357_stmt, selfIdent, newEnv, (isLast) && ((_1355_i) == ((new BigInteger((_1356_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out111, out _out112, out _out113);
        _1364_stmtExpr = _out111;
        _1365_recIdents = _out112;
        _1366_newEnv2 = _out113;
        newEnv = _1366_newEnv2;
        DAST._IStatement _source63 = _1357_stmt;
        bool unmatched63 = true;
        if (unmatched63) {
          if (_source63.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1367_name = _source63.dtor_name;
            DAST._IType _1368___v66 = _source63.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> _1369___v67 = _source63.dtor_maybeValue;
            unmatched63 = false;
            {
              _1354_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1354_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_1367_name)));
            }
          }
        }
        if (unmatched63) {
          DAST._IStatement _1370___v68 = _source63;
          unmatched63 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1365_recIdents, _1354_declarations));
        generated = (generated).Then(_1364_stmtExpr);
        _1355_i = (_1355_i) + (BigInteger.One);
      }
    }
    public void GenAssignLhs(DAST._IAssignLhs lhs, RAST._IExpr rhs, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, out RAST._IExpr generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      newEnv = env;
      DAST._IAssignLhs _source64 = lhs;
      bool unmatched64 = true;
      if (unmatched64) {
        if (_source64.is_Ident) {
          Dafny.ISequence<Dafny.Rune> ident1 = _source64.dtor_ident;
          Dafny.ISequence<Dafny.Rune> _1371_id = ident1;
          unmatched64 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1372_idRust;
            _1372_idRust = DCOMP.__default.escapeName(_1371_id);
            if (((env).IsBorrowed(_1372_idRust)) || ((env).IsBorrowedMut(_1372_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1372_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1372_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1372_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched64) {
        if (_source64.is_Select) {
          DAST._IExpression _1373_on = _source64.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1374_field = _source64.dtor_field;
          unmatched64 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1375_fieldName;
            _1375_fieldName = DCOMP.__default.escapeName(_1374_field);
            RAST._IExpr _1376_onExpr;
            DCOMP._IOwnership _1377_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1378_recIdents;
            RAST._IExpr _out114;
            DCOMP._IOwnership _out115;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
            (this).GenExpr(_1373_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out114, out _out115, out _out116);
            _1376_onExpr = _out114;
            _1377_onOwned = _out115;
            _1378_recIdents = _out116;
            generated = RAST.__default.AssignMember(((this).modify__macro).Apply1(_1376_onExpr), _1375_fieldName, rhs);
            RAST._IExpr _source65 = _1376_onExpr;
            bool unmatched65 = true;
            if (unmatched65) {
              bool disjunctiveMatch9 = false;
              if (_source65.is_Call) {
                RAST._IExpr obj3 = _source65.dtor_obj;
                if (obj3.is_Select) {
                  RAST._IExpr obj4 = obj3.dtor_obj;
                  if (obj4.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name18 = obj4.dtor_name;
                    if (object.Equals(name18, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      Dafny.ISequence<Dafny.Rune> name19 = obj3.dtor_name;
                      if (object.Equals(name19, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))) {
                        Dafny.ISequence<RAST._IExpr> _1379___v69 = _source65.dtor_arguments;
                        disjunctiveMatch9 = true;
                      }
                    }
                  }
                }
              }
              if (_source65.is_Identifier) {
                Dafny.ISequence<Dafny.Rune> name20 = _source65.dtor_name;
                if (object.Equals(name20, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                  disjunctiveMatch9 = true;
                }
              }
              if (disjunctiveMatch9) {
                unmatched65 = false;
                Dafny.ISequence<Dafny.Rune> _1380_isAssignedVar;
                _1380_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1375_fieldName);
                if (((newEnv).dtor_names).Contains(_1380_isAssignedVar)) {
                  generated = ((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1375_fieldName), RAST.Expr.create_Identifier(_1380_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1380_isAssignedVar);
                }
              }
            }
            if (unmatched65) {
              RAST._IExpr _1381___v70 = _source65;
              unmatched65 = false;
            }
            readIdents = _1378_recIdents;
            needsIIFE = false;
          }
        }
      }
      if (unmatched64) {
        DAST._IExpression _1382_on = _source64.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1383_indices = _source64.dtor_indices;
        unmatched64 = false;
        {
          RAST._IExpr _1384_onExpr;
          DCOMP._IOwnership _1385_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1386_recIdents;
          RAST._IExpr _out117;
          DCOMP._IOwnership _out118;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out119;
          (this).GenExpr(_1382_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out117, out _out118, out _out119);
          _1384_onExpr = _out117;
          _1385_onOwned = _out118;
          _1386_recIdents = _out119;
          readIdents = _1386_recIdents;
          _1384_onExpr = ((this).modify__macro).Apply1(_1384_onExpr);
          RAST._IExpr _1387_r;
          _1387_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1388_indicesExpr;
          _1388_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi28 = new BigInteger((_1383_indices).Count);
          for (BigInteger _1389_i = BigInteger.Zero; _1389_i < _hi28; _1389_i++) {
            RAST._IExpr _1390_idx;
            DCOMP._IOwnership _1391___v71;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1392_recIdentsIdx;
            RAST._IExpr _out120;
            DCOMP._IOwnership _out121;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out122;
            (this).GenExpr((_1383_indices).Select(_1389_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out120, out _out121, out _out122);
            _1390_idx = _out120;
            _1391___v71 = _out121;
            _1392_recIdentsIdx = _out122;
            Dafny.ISequence<Dafny.Rune> _1393_varName;
            _1393_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1389_i));
            _1388_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1388_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1393_varName)));
            _1387_r = (_1387_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1393_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<usize as ::dafny_runtime::NumCast>::from("), (_1390_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"))))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1392_recIdentsIdx);
          }
          if ((new BigInteger((_1383_indices).Count)) > (BigInteger.One)) {
            _1384_onExpr = (_1384_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1394_rhs;
          _1394_rhs = rhs;
          var _pat_let_tv105 = env;
          if (((_1384_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1384_onExpr).LhsIdentifierName(), _pat_let11_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let11_0, _1395_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv105).GetType(_1395_name), _pat_let12_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let12_0, _1396_tpe => ((_1396_tpe).is_Some) && (((_1396_tpe).dtor_value).IsUninitArray())))))))) {
            _1394_rhs = RAST.__default.MaybeUninitNew(_1394_rhs);
          }
          generated = (_1387_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1384_onExpr, _1388_indicesExpr)), _1394_rhs));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source66 = stmt;
      bool unmatched66 = true;
      if (unmatched66) {
        if (_source66.is_ConstructorNewSeparator) {
          Dafny.ISequence<DAST._IFormal> _1397_fields = _source66.dtor_fields;
          unmatched66 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi29 = new BigInteger((_1397_fields).Count);
            for (BigInteger _1398_i = BigInteger.Zero; _1398_i < _hi29; _1398_i++) {
              DAST._IFormal _1399_field;
              _1399_field = (_1397_fields).Select(_1398_i);
              Dafny.ISequence<Dafny.Rune> _1400_fieldName;
              _1400_fieldName = DCOMP.__default.escapeName((_1399_field).dtor_name);
              RAST._IType _1401_fieldTyp;
              RAST._IType _out123;
              _out123 = (this).GenType((_1399_field).dtor_typ, false, false);
              _1401_fieldTyp = _out123;
              Dafny.ISequence<Dafny.Rune> _1402_isAssignedVar;
              _1402_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1400_fieldName);
              if (((newEnv).dtor_names).Contains(_1402_isAssignedVar)) {
                RAST._IExpr _1403_rhs;
                DCOMP._IOwnership _1404___v72;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1405___v73;
                RAST._IExpr _out124;
                DCOMP._IOwnership _out125;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1399_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out124, out _out125, out _out126);
                _1403_rhs = _out124;
                _1404___v72 = _out125;
                _1405___v73 = _out126;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1402_isAssignedVar));
                generated = (generated).Then(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_if_uninit!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1400_fieldName), RAST.Expr.create_Identifier(_1402_isAssignedVar), _1403_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1402_isAssignedVar);
              }
            }
          }
        }
      }
      if (unmatched66) {
        if (_source66.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1406_name = _source66.dtor_name;
          DAST._IType _1407_typ = _source66.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source66.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1408_expression = maybeValue1.dtor_value;
            unmatched66 = false;
            {
              RAST._IType _1409_tpe;
              RAST._IType _out127;
              _out127 = (this).GenType(_1407_typ, true, false);
              _1409_tpe = _out127;
              Dafny.ISequence<Dafny.Rune> _1410_varName;
              _1410_varName = DCOMP.__default.escapeName(_1406_name);
              bool _1411_hasCopySemantics;
              _1411_hasCopySemantics = (_1409_tpe).CanReadWithoutClone();
              if (((_1408_expression).is_InitializationValue) && (!(_1411_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1410_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).ApplyType1(_1409_tpe)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1410_varName, RAST.__default.MaybePlaceboType(_1409_tpe));
              } else {
                RAST._IExpr _1412_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1413_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1408_expression).is_InitializationValue) && ((_1409_tpe).IsObjectOrPointer())) {
                  _1412_expr = (_1409_tpe).ToNullExpr();
                  _1413_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1414_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out128;
                  DCOMP._IOwnership _out129;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out130;
                  (this).GenExpr(_1408_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out128, out _out129, out _out130);
                  _1412_expr = _out128;
                  _1414_exprOwnership = _out129;
                  _1413_recIdents = _out130;
                }
                readIdents = _1413_recIdents;
                _1409_tpe = (((_1408_expression).is_NewUninitArray) ? ((_1409_tpe).TypeAtInitialization()) : (_1409_tpe));
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_1406_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1409_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1412_expr));
                newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_1406_name), _1409_tpe);
              }
            }
          }
        }
      }
      if (unmatched66) {
        if (_source66.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1415_name = _source66.dtor_name;
          DAST._IType _1416_typ = _source66.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source66.dtor_maybeValue;
          if (maybeValue2.is_None) {
            unmatched66 = false;
            {
              DAST._IStatement _1417_newStmt;
              _1417_newStmt = DAST.Statement.create_DeclareVar(_1415_name, _1416_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1416_typ)));
              RAST._IExpr _out131;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out132;
              DCOMP._IEnvironment _out133;
              (this).GenStmt(_1417_newStmt, selfIdent, env, isLast, earlyReturn, out _out131, out _out132, out _out133);
              generated = _out131;
              readIdents = _out132;
              newEnv = _out133;
            }
          }
        }
      }
      if (unmatched66) {
        if (_source66.is_Assign) {
          DAST._IAssignLhs _1418_lhs = _source66.dtor_lhs;
          DAST._IExpression _1419_expression = _source66.dtor_value;
          unmatched66 = false;
          {
            RAST._IExpr _1420_exprGen;
            DCOMP._IOwnership _1421___v74;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1422_exprIdents;
            RAST._IExpr _out134;
            DCOMP._IOwnership _out135;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out136;
            (this).GenExpr(_1419_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out134, out _out135, out _out136);
            _1420_exprGen = _out134;
            _1421___v74 = _out135;
            _1422_exprIdents = _out136;
            if ((_1418_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1423_rustId;
              _1423_rustId = DCOMP.__default.escapeName(((_1418_lhs).dtor_ident));
              Std.Wrappers._IOption<RAST._IType> _1424_tpe;
              _1424_tpe = (env).GetType(_1423_rustId);
              if (((_1424_tpe).is_Some) && ((((_1424_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1420_exprGen = RAST.__default.MaybePlacebo(_1420_exprGen);
              }
            }
            RAST._IExpr _1425_lhsGen;
            bool _1426_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1427_recIdents;
            DCOMP._IEnvironment _1428_resEnv;
            RAST._IExpr _out137;
            bool _out138;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out139;
            DCOMP._IEnvironment _out140;
            (this).GenAssignLhs(_1418_lhs, _1420_exprGen, selfIdent, env, out _out137, out _out138, out _out139, out _out140);
            _1425_lhsGen = _out137;
            _1426_needsIIFE = _out138;
            _1427_recIdents = _out139;
            _1428_resEnv = _out140;
            generated = _1425_lhsGen;
            newEnv = _1428_resEnv;
            if (_1426_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1427_recIdents, _1422_exprIdents);
          }
        }
      }
      if (unmatched66) {
        if (_source66.is_If) {
          DAST._IExpression _1429_cond = _source66.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1430_thnDafny = _source66.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1431_elsDafny = _source66.dtor_els;
          unmatched66 = false;
          {
            RAST._IExpr _1432_cond;
            DCOMP._IOwnership _1433___v75;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1434_recIdents;
            RAST._IExpr _out141;
            DCOMP._IOwnership _out142;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out143;
            (this).GenExpr(_1429_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out141, out _out142, out _out143);
            _1432_cond = _out141;
            _1433___v75 = _out142;
            _1434_recIdents = _out143;
            Dafny.ISequence<Dafny.Rune> _1435_condString;
            _1435_condString = (_1432_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1434_recIdents;
            RAST._IExpr _1436_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1437_thnIdents;
            DCOMP._IEnvironment _1438_thnEnv;
            RAST._IExpr _out144;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out145;
            DCOMP._IEnvironment _out146;
            (this).GenStmts(_1430_thnDafny, selfIdent, env, isLast, earlyReturn, out _out144, out _out145, out _out146);
            _1436_thn = _out144;
            _1437_thnIdents = _out145;
            _1438_thnEnv = _out146;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1437_thnIdents);
            RAST._IExpr _1439_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1440_elsIdents;
            DCOMP._IEnvironment _1441_elsEnv;
            RAST._IExpr _out147;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out148;
            DCOMP._IEnvironment _out149;
            (this).GenStmts(_1431_elsDafny, selfIdent, env, isLast, earlyReturn, out _out147, out _out148, out _out149);
            _1439_els = _out147;
            _1440_elsIdents = _out148;
            _1441_elsEnv = _out149;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1440_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1432_cond, _1436_thn, _1439_els);
          }
        }
      }
      if (unmatched66) {
        if (_source66.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1442_lbl = _source66.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1443_body = _source66.dtor_body;
          unmatched66 = false;
          {
            RAST._IExpr _1444_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1445_bodyIdents;
            DCOMP._IEnvironment _1446_env2;
            RAST._IExpr _out150;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out151;
            DCOMP._IEnvironment _out152;
            (this).GenStmts(_1443_body, selfIdent, env, isLast, earlyReturn, out _out150, out _out151, out _out152);
            _1444_body = _out150;
            _1445_bodyIdents = _out151;
            _1446_env2 = _out152;
            readIdents = _1445_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1442_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1444_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched66) {
        if (_source66.is_While) {
          DAST._IExpression _1447_cond = _source66.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1448_body = _source66.dtor_body;
          unmatched66 = false;
          {
            RAST._IExpr _1449_cond;
            DCOMP._IOwnership _1450___v76;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1451_recIdents;
            RAST._IExpr _out153;
            DCOMP._IOwnership _out154;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out155;
            (this).GenExpr(_1447_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out153, out _out154, out _out155);
            _1449_cond = _out153;
            _1450___v76 = _out154;
            _1451_recIdents = _out155;
            readIdents = _1451_recIdents;
            RAST._IExpr _1452_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1453_bodyIdents;
            DCOMP._IEnvironment _1454_bodyEnv;
            RAST._IExpr _out156;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out157;
            DCOMP._IEnvironment _out158;
            (this).GenStmts(_1448_body, selfIdent, env, false, earlyReturn, out _out156, out _out157, out _out158);
            _1452_bodyExpr = _out156;
            _1453_bodyIdents = _out157;
            _1454_bodyEnv = _out158;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1453_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1449_cond), _1452_bodyExpr);
          }
        }
      }
      if (unmatched66) {
        if (_source66.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1455_boundName = _source66.dtor_boundName;
          DAST._IType _1456_boundType = _source66.dtor_boundType;
          DAST._IExpression _1457_overExpr = _source66.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1458_body = _source66.dtor_body;
          unmatched66 = false;
          {
            RAST._IExpr _1459_over;
            DCOMP._IOwnership _1460___v77;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1461_recIdents;
            RAST._IExpr _out159;
            DCOMP._IOwnership _out160;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out161;
            (this).GenExpr(_1457_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out159, out _out160, out _out161);
            _1459_over = _out159;
            _1460___v77 = _out160;
            _1461_recIdents = _out161;
            if (((_1457_overExpr).is_MapBoundedPool) || ((_1457_overExpr).is_SetBoundedPool)) {
              _1459_over = ((_1459_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1462_boundTpe;
            RAST._IType _out162;
            _out162 = (this).GenType(_1456_boundType, false, false);
            _1462_boundTpe = _out162;
            readIdents = _1461_recIdents;
            Dafny.ISequence<Dafny.Rune> _1463_boundRName;
            _1463_boundRName = DCOMP.__default.escapeName(_1455_boundName);
            RAST._IExpr _1464_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1465_bodyIdents;
            DCOMP._IEnvironment _1466_bodyEnv;
            RAST._IExpr _out163;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out164;
            DCOMP._IEnvironment _out165;
            (this).GenStmts(_1458_body, selfIdent, (env).AddAssigned(_1463_boundRName, _1462_boundTpe), false, earlyReturn, out _out163, out _out164, out _out165);
            _1464_bodyExpr = _out163;
            _1465_bodyIdents = _out164;
            _1466_bodyEnv = _out165;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1465_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1463_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1463_boundRName, _1459_over, _1464_bodyExpr);
          }
        }
      }
      if (unmatched66) {
        if (_source66.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1467_toLabel = _source66.dtor_toLabel;
          unmatched66 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source67 = _1467_toLabel;
            bool unmatched67 = true;
            if (unmatched67) {
              if (_source67.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1468_lbl = _source67.dtor_value;
                unmatched67 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1468_lbl)));
                }
              }
            }
            if (unmatched67) {
              unmatched67 = false;
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched66) {
        if (_source66.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1469_body = _source66.dtor_body;
          unmatched66 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
            }
            newEnv = env;
            BigInteger _hi30 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1470_paramI = BigInteger.Zero; _1470_paramI < _hi30; _1470_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1471_param;
              _1471_param = ((env).dtor_names).Select(_1470_paramI);
              RAST._IExpr _1472_paramInit;
              DCOMP._IOwnership _1473___v78;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1474___v79;
              RAST._IExpr _out166;
              DCOMP._IOwnership _out167;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out168;
              (this).GenIdent(_1471_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out166, out _out167, out _out168);
              _1472_paramInit = _out166;
              _1473___v78 = _out167;
              _1474___v79 = _out168;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1471_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1472_paramInit)));
              if (((env).dtor_types).Contains(_1471_param)) {
                RAST._IType _1475_declaredType;
                _1475_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1471_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1471_param, _1475_declaredType);
              }
            }
            RAST._IExpr _1476_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1477_bodyIdents;
            DCOMP._IEnvironment _1478_bodyEnv;
            RAST._IExpr _out169;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out170;
            DCOMP._IEnvironment _out171;
            (this).GenStmts(_1469_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), newEnv, false, earlyReturn, out _out169, out _out170, out _out171);
            _1476_bodyExpr = _out169;
            _1477_bodyIdents = _out170;
            _1478_bodyEnv = _out171;
            readIdents = _1477_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1476_bodyExpr)));
          }
        }
      }
      if (unmatched66) {
        if (_source66.is_JumpTailCallStart) {
          unmatched66 = false;
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched66) {
        if (_source66.is_Call) {
          DAST._IExpression _1479_on = _source66.dtor_on;
          DAST._ICallName _1480_name = _source66.dtor_callName;
          Dafny.ISequence<DAST._IType> _1481_typeArgs = _source66.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1482_args = _source66.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1483_maybeOutVars = _source66.dtor_outs;
          unmatched66 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IExpr _1484_onExpr;
            DCOMP._IOwnership _1485___v80;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1486_enclosingIdents;
            RAST._IExpr _out172;
            DCOMP._IOwnership _out173;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out174;
            (this).GenExpr(_1479_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out172, out _out173, out _out174);
            _1484_onExpr = _out172;
            _1485___v80 = _out173;
            _1486_enclosingIdents = _out174;
            Dafny.ISequence<RAST._IType> _1487_typeArgsR;
            _1487_typeArgsR = Dafny.Sequence<RAST._IType>.FromElements();
            if ((new BigInteger((_1481_typeArgs).Count)) >= (BigInteger.One)) {
              BigInteger _1488_typeI;
              _1488_typeI = BigInteger.Zero;
              while ((_1488_typeI) < (new BigInteger((_1481_typeArgs).Count))) {
                RAST._IType _1489_tpe;
                RAST._IType _out175;
                _out175 = (this).GenType((_1481_typeArgs).Select(_1488_typeI), false, false);
                _1489_tpe = _out175;
                _1487_typeArgsR = Dafny.Sequence<RAST._IType>.Concat(_1487_typeArgsR, Dafny.Sequence<RAST._IType>.FromElements(_1489_tpe));
                _1488_typeI = (_1488_typeI) + (BigInteger.One);
              }
            }
            Dafny.ISequence<RAST._IExpr> _1490_argExprs;
            _1490_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi31 = new BigInteger((_1482_args).Count);
            for (BigInteger _1491_i = BigInteger.Zero; _1491_i < _hi31; _1491_i++) {
              DCOMP._IOwnership _1492_argOwnership;
              _1492_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              if (((_1480_name).is_CallName) && ((_1491_i) < (new BigInteger((((_1480_name).dtor_signature)).Count)))) {
                RAST._IType _1493_tpe;
                RAST._IType _out176;
                _out176 = (this).GenType(((((_1480_name).dtor_signature)).Select(_1491_i)).dtor_typ, false, false);
                _1493_tpe = _out176;
                if ((_1493_tpe).CanReadWithoutClone()) {
                  _1492_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
                }
              }
              RAST._IExpr _1494_argExpr;
              DCOMP._IOwnership _1495_ownership;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1496_argIdents;
              RAST._IExpr _out177;
              DCOMP._IOwnership _out178;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out179;
              (this).GenExpr((_1482_args).Select(_1491_i), selfIdent, env, _1492_argOwnership, out _out177, out _out178, out _out179);
              _1494_argExpr = _out177;
              _1495_ownership = _out178;
              _1496_argIdents = _out179;
              _1490_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1490_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1494_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1496_argIdents);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1486_enclosingIdents);
            Dafny.ISequence<Dafny.Rune> _1497_renderedName;
            _1497_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
              DAST._ICallName _source68 = _1480_name;
              bool unmatched68 = true;
              if (unmatched68) {
                if (_source68.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _1498_name = _source68.dtor_name;
                  Std.Wrappers._IOption<DAST._IType> _1499___v81 = _source68.dtor_onType;
                  Std.Wrappers._IOption<DAST._IFormal> _1500___v82 = _source68.dtor_receiverArgs;
                  Dafny.ISequence<DAST._IFormal> _1501___v83 = _source68.dtor_signature;
                  unmatched68 = false;
                  return DCOMP.__default.escapeName(_1498_name);
                }
              }
              if (unmatched68) {
                bool disjunctiveMatch10 = false;
                if (_source68.is_MapBuilderAdd) {
                  disjunctiveMatch10 = true;
                }
                if (_source68.is_SetBuilderAdd) {
                  disjunctiveMatch10 = true;
                }
                if (disjunctiveMatch10) {
                  unmatched68 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                }
              }
              if (unmatched68) {
                bool disjunctiveMatch11 = false;
                disjunctiveMatch11 = true;
                disjunctiveMatch11 = true;
                if (disjunctiveMatch11) {
                  unmatched68 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                }
              }
              throw new System.Exception("unexpected control point");
            }))();
            DAST._IExpression _source69 = _1479_on;
            bool unmatched69 = true;
            if (unmatched69) {
              if (_source69.is_Companion) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1502___v84 = _source69.dtor_Companion_a0;
                unmatched69 = false;
                {
                  _1484_onExpr = (_1484_onExpr).MSel(_1497_renderedName);
                }
              }
            }
            if (unmatched69) {
              DAST._IExpression _1503___v85 = _source69;
              unmatched69 = false;
              {
                DAST._ICallName _source70 = _1480_name;
                bool unmatched70 = true;
                if (unmatched70) {
                  if (_source70.is_CallName) {
                    Dafny.ISequence<Dafny.Rune> _1504___v86 = _source70.dtor_name;
                    Std.Wrappers._IOption<DAST._IType> onType0 = _source70.dtor_onType;
                    if (onType0.is_Some) {
                      DAST._IType _1505_tpe = onType0.dtor_value;
                      Std.Wrappers._IOption<DAST._IFormal> _1506___v87 = _source70.dtor_receiverArgs;
                      Dafny.ISequence<DAST._IFormal> _1507___v88 = _source70.dtor_signature;
                      unmatched70 = false;
                      RAST._IType _1508_typ;
                      RAST._IType _out180;
                      _out180 = (this).GenType(_1505_tpe, false, false);
                      _1508_typ = _out180;
                      if ((_1508_typ).IsObjectOrPointer()) {
                        if ((_1508_typ).IsObject()) {
                          _1484_onExpr = ((_1484_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                        }
                        _1484_onExpr = ((this).modify__macro).Apply1(_1484_onExpr);
                      }
                    }
                  }
                }
                if (unmatched70) {
                  DAST._ICallName _1509___v89 = _source70;
                  unmatched70 = false;
                }
                _1484_onExpr = (_1484_onExpr).Sel(_1497_renderedName);
              }
            }
            generated = _1484_onExpr;
            if ((new BigInteger((_1487_typeArgsR).Count)).Sign == 1) {
              generated = (generated).ApplyType(_1487_typeArgsR);
            }
            generated = (generated).Apply(_1490_argExprs);
            if (((_1483_maybeOutVars).is_Some) && ((new BigInteger(((_1483_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1510_outVar;
              _1510_outVar = DCOMP.__default.escapeName((((_1483_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
              if (!((env).CanReadWithoutClone(_1510_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1510_outVar, generated);
            } else if (((_1483_maybeOutVars).is_None) || ((new BigInteger(((_1483_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1511_tmpVar;
              _1511_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1512_tmpId;
              _1512_tmpId = RAST.Expr.create_Identifier(_1511_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1511_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1513_outVars;
              _1513_outVars = (_1483_maybeOutVars).dtor_value;
              BigInteger _hi32 = new BigInteger((_1513_outVars).Count);
              for (BigInteger _1514_outI = BigInteger.Zero; _1514_outI < _hi32; _1514_outI++) {
                Dafny.ISequence<Dafny.Rune> _1515_outVar;
                _1515_outVar = DCOMP.__default.escapeName(((_1513_outVars).Select(_1514_outI)));
                RAST._IExpr _1516_rhs;
                _1516_rhs = (_1512_tmpId).Sel(Std.Strings.__default.OfNat(_1514_outI));
                if (!((env).CanReadWithoutClone(_1515_outVar))) {
                  _1516_rhs = RAST.__default.MaybePlacebo(_1516_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1515_outVar, _1516_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched66) {
        if (_source66.is_Return) {
          DAST._IExpression _1517_exprDafny = _source66.dtor_expr;
          unmatched66 = false;
          {
            RAST._IExpr _1518_expr;
            DCOMP._IOwnership _1519___v90;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1520_recIdents;
            RAST._IExpr _out181;
            DCOMP._IOwnership _out182;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out183;
            (this).GenExpr(_1517_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out181, out _out182, out _out183);
            _1518_expr = _out181;
            _1519___v90 = _out182;
            _1520_recIdents = _out183;
            readIdents = _1520_recIdents;
            if (isLast) {
              generated = _1518_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1518_expr));
            }
            newEnv = env;
          }
        }
      }
      if (unmatched66) {
        if (_source66.is_EarlyReturn) {
          unmatched66 = false;
          {
            generated = earlyReturn;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched66) {
        if (_source66.is_Halt) {
          unmatched66 = false;
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched66) {
        DAST._IExpression _1521_e = _source66.dtor_Print_a0;
        unmatched66 = false;
        {
          RAST._IExpr _1522_printedExpr;
          DCOMP._IOwnership _1523_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1524_recIdents;
          RAST._IExpr _out184;
          DCOMP._IOwnership _out185;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out186;
          (this).GenExpr(_1521_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out184, out _out185, out _out186);
          _1522_printedExpr = _out184;
          _1523_recOwnership = _out185;
          _1524_recIdents = _out186;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1522_printedExpr)));
          readIdents = _1524_recIdents;
          newEnv = env;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source71 = range;
      bool unmatched71 = true;
      if (unmatched71) {
        if (_source71.is_NoRange) {
          unmatched71 = false;
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      if (unmatched71) {
        if (_source71.is_U8) {
          unmatched71 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      if (unmatched71) {
        if (_source71.is_U16) {
          unmatched71 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      if (unmatched71) {
        if (_source71.is_U32) {
          unmatched71 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      if (unmatched71) {
        if (_source71.is_U64) {
          unmatched71 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      if (unmatched71) {
        if (_source71.is_U128) {
          unmatched71 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      if (unmatched71) {
        if (_source71.is_I8) {
          unmatched71 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      if (unmatched71) {
        if (_source71.is_I16) {
          unmatched71 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      if (unmatched71) {
        if (_source71.is_I32) {
          unmatched71 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      if (unmatched71) {
        if (_source71.is_I64) {
          unmatched71 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      if (unmatched71) {
        if (_source71.is_I128) {
          unmatched71 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
        }
      }
      if (unmatched71) {
        DAST._INewtypeRange _1525___v91 = _source71;
        unmatched71 = false;
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
        RAST._IExpr _out187;
        DCOMP._IOwnership _out188;
        DCOMP.COMP.FromOwned(r, expectedOwnership, out _out187, out _out188);
        @out = _out187;
        resultingOwnership = _out188;
        return ;
      } else if (object.Equals(ownership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        RAST._IExpr _out189;
        DCOMP._IOwnership _out190;
        DCOMP.COMP.FromOwned(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), r, DAST.Format.UnaryOpFormat.create_NoFormat()), expectedOwnership, out _out189, out _out190);
        @out = _out189;
        resultingOwnership = _out190;
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
    public void GenExprLiteral(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source72 = e;
      bool unmatched72 = true;
      if (unmatched72) {
        if (_source72.is_Literal) {
          DAST._ILiteral _h150 = _source72.dtor_Literal_a0;
          if (_h150.is_BoolLiteral) {
            bool _1526_b = _h150.dtor_BoolLiteral_a0;
            unmatched72 = false;
            {
              RAST._IExpr _out191;
              DCOMP._IOwnership _out192;
              DCOMP.COMP.FromOwned(RAST.Expr.create_LiteralBool(_1526_b), expectedOwnership, out _out191, out _out192);
              r = _out191;
              resultingOwnership = _out192;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched72) {
        if (_source72.is_Literal) {
          DAST._ILiteral _h151 = _source72.dtor_Literal_a0;
          if (_h151.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1527_i = _h151.dtor_IntLiteral_a0;
            DAST._IType _1528_t = _h151.dtor_IntLiteral_a1;
            unmatched72 = false;
            {
              DAST._IType _source73 = _1528_t;
              bool unmatched73 = true;
              if (unmatched73) {
                if (_source73.is_Primitive) {
                  DAST._IPrimitive _h90 = _source73.dtor_Primitive_a0;
                  if (_h90.is_Int) {
                    unmatched73 = false;
                    {
                      if ((new BigInteger((_1527_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1527_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1527_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched73) {
                DAST._IType _1529_o = _source73;
                unmatched73 = false;
                {
                  RAST._IType _1530_genType;
                  RAST._IType _out193;
                  _out193 = (this).GenType(_1529_o, false, false);
                  _1530_genType = _out193;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1527_i), _1530_genType);
                }
              }
              RAST._IExpr _out194;
              DCOMP._IOwnership _out195;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out194, out _out195);
              r = _out194;
              resultingOwnership = _out195;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched72) {
        if (_source72.is_Literal) {
          DAST._ILiteral _h152 = _source72.dtor_Literal_a0;
          if (_h152.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1531_n = _h152.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1532_d = _h152.dtor_DecLiteral_a1;
            DAST._IType _1533_t = _h152.dtor_DecLiteral_a2;
            unmatched72 = false;
            {
              DAST._IType _source74 = _1533_t;
              bool unmatched74 = true;
              if (unmatched74) {
                if (_source74.is_Primitive) {
                  DAST._IPrimitive _h91 = _source74.dtor_Primitive_a0;
                  if (_h91.is_Real) {
                    unmatched74 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1531_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1532_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched74) {
                DAST._IType _1534_o = _source74;
                unmatched74 = false;
                {
                  RAST._IType _1535_genType;
                  RAST._IType _out196;
                  _out196 = (this).GenType(_1534_o, false, false);
                  _1535_genType = _out196;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1531_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1532_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1535_genType);
                }
              }
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
      if (unmatched72) {
        if (_source72.is_Literal) {
          DAST._ILiteral _h153 = _source72.dtor_Literal_a0;
          if (_h153.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1536_l = _h153.dtor_StringLiteral_a0;
            bool _1537_verbatim = _h153.dtor_verbatim;
            unmatched72 = false;
            {
              if (_1537_verbatim) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Verbatim strings prefixed by @ not supported yet."));
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1536_l, false, _1537_verbatim));
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
      if (unmatched72) {
        if (_source72.is_Literal) {
          DAST._ILiteral _h154 = _source72.dtor_Literal_a0;
          if (_h154.is_CharLiteralUTF16) {
            BigInteger _1538_c = _h154.dtor_CharLiteralUTF16_a0;
            unmatched72 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1538_c));
              r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
              RAST._IExpr _out201;
              DCOMP._IOwnership _out202;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out201, out _out202);
              r = _out201;
              resultingOwnership = _out202;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched72) {
        if (_source72.is_Literal) {
          DAST._ILiteral _h155 = _source72.dtor_Literal_a0;
          if (_h155.is_CharLiteral) {
            Dafny.Rune _1539_c = _h155.dtor_CharLiteral_a0;
            unmatched72 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1539_c).Value)));
              if (!((this).UnicodeChars)) {
                r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              } else {
                r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
              RAST._IExpr _out203;
              DCOMP._IOwnership _out204;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out203, out _out204);
              r = _out203;
              resultingOwnership = _out204;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched72) {
        DAST._ILiteral _h156 = _source72.dtor_Literal_a0;
        DAST._IType _1540_tpe = _h156.dtor_Null_a0;
        unmatched72 = false;
        {
          RAST._IType _1541_tpeGen;
          RAST._IType _out205;
          _out205 = (this).GenType(_1540_tpe, false, false);
          _1541_tpeGen = _out205;
          r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None")), _1541_tpeGen);
          RAST._IExpr _out206;
          DCOMP._IOwnership _out207;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out206, out _out207);
          r = _out206;
          resultingOwnership = _out207;
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
      DAST._IBinOp _1542_op = _let_tmp_rhs52.dtor_op;
      DAST._IExpression _1543_lExpr = _let_tmp_rhs52.dtor_left;
      DAST._IExpression _1544_rExpr = _let_tmp_rhs52.dtor_right;
      DAST.Format._IBinaryOpFormat _1545_format = _let_tmp_rhs52.dtor_format2;
      bool _1546_becomesLeftCallsRight;
      _1546_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source75 = _1542_op;
        bool unmatched75 = true;
        if (unmatched75) {
          bool disjunctiveMatch12 = false;
          if (_source75.is_SetMerge) {
            disjunctiveMatch12 = true;
          }
          if (_source75.is_SetSubtraction) {
            disjunctiveMatch12 = true;
          }
          if (_source75.is_SetIntersection) {
            disjunctiveMatch12 = true;
          }
          if (_source75.is_SetDisjoint) {
            disjunctiveMatch12 = true;
          }
          if (_source75.is_MapMerge) {
            disjunctiveMatch12 = true;
          }
          if (_source75.is_MapSubtraction) {
            disjunctiveMatch12 = true;
          }
          if (_source75.is_MultisetMerge) {
            disjunctiveMatch12 = true;
          }
          if (_source75.is_MultisetSubtraction) {
            disjunctiveMatch12 = true;
          }
          if (_source75.is_MultisetIntersection) {
            disjunctiveMatch12 = true;
          }
          if (_source75.is_MultisetDisjoint) {
            disjunctiveMatch12 = true;
          }
          if (_source75.is_Concat) {
            disjunctiveMatch12 = true;
          }
          if (disjunctiveMatch12) {
            unmatched75 = false;
            return true;
          }
        }
        if (unmatched75) {
          DAST._IBinOp _1547___v92 = _source75;
          unmatched75 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1548_becomesRightCallsLeft;
      _1548_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source76 = _1542_op;
        bool unmatched76 = true;
        if (unmatched76) {
          if (_source76.is_In) {
            unmatched76 = false;
            return true;
          }
        }
        if (unmatched76) {
          DAST._IBinOp _1549___v93 = _source76;
          unmatched76 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1550_becomesCallLeftRight;
      _1550_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source77 = _1542_op;
        bool unmatched77 = true;
        if (unmatched77) {
          if (_source77.is_Eq) {
            bool referential0 = _source77.dtor_referential;
            if ((referential0) == (true)) {
              bool nullable0 = _source77.dtor_nullable;
              if ((nullable0) == (false)) {
                unmatched77 = false;
                return true;
              }
            }
          }
        }
        if (unmatched77) {
          if (_source77.is_SetMerge) {
            unmatched77 = false;
            return true;
          }
        }
        if (unmatched77) {
          if (_source77.is_SetSubtraction) {
            unmatched77 = false;
            return true;
          }
        }
        if (unmatched77) {
          if (_source77.is_SetIntersection) {
            unmatched77 = false;
            return true;
          }
        }
        if (unmatched77) {
          if (_source77.is_SetDisjoint) {
            unmatched77 = false;
            return true;
          }
        }
        if (unmatched77) {
          if (_source77.is_MapMerge) {
            unmatched77 = false;
            return true;
          }
        }
        if (unmatched77) {
          if (_source77.is_MapSubtraction) {
            unmatched77 = false;
            return true;
          }
        }
        if (unmatched77) {
          if (_source77.is_MultisetMerge) {
            unmatched77 = false;
            return true;
          }
        }
        if (unmatched77) {
          if (_source77.is_MultisetSubtraction) {
            unmatched77 = false;
            return true;
          }
        }
        if (unmatched77) {
          if (_source77.is_MultisetIntersection) {
            unmatched77 = false;
            return true;
          }
        }
        if (unmatched77) {
          if (_source77.is_MultisetDisjoint) {
            unmatched77 = false;
            return true;
          }
        }
        if (unmatched77) {
          if (_source77.is_Concat) {
            unmatched77 = false;
            return true;
          }
        }
        if (unmatched77) {
          DAST._IBinOp _1551___v94 = _source77;
          unmatched77 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      DCOMP._IOwnership _1552_expectedLeftOwnership;
      _1552_expectedLeftOwnership = ((_1546_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1548_becomesRightCallsLeft) || (_1550_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1553_expectedRightOwnership;
      _1553_expectedRightOwnership = (((_1546_becomesLeftCallsRight) || (_1550_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1548_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1554_left;
      DCOMP._IOwnership _1555___v95;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1556_recIdentsL;
      RAST._IExpr _out208;
      DCOMP._IOwnership _out209;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out210;
      (this).GenExpr(_1543_lExpr, selfIdent, env, _1552_expectedLeftOwnership, out _out208, out _out209, out _out210);
      _1554_left = _out208;
      _1555___v95 = _out209;
      _1556_recIdentsL = _out210;
      RAST._IExpr _1557_right;
      DCOMP._IOwnership _1558___v96;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1559_recIdentsR;
      RAST._IExpr _out211;
      DCOMP._IOwnership _out212;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out213;
      (this).GenExpr(_1544_rExpr, selfIdent, env, _1553_expectedRightOwnership, out _out211, out _out212, out _out213);
      _1557_right = _out211;
      _1558___v96 = _out212;
      _1559_recIdentsR = _out213;
      DAST._IBinOp _source78 = _1542_op;
      bool unmatched78 = true;
      if (unmatched78) {
        if (_source78.is_In) {
          unmatched78 = false;
          {
            r = ((_1557_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1554_left);
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_SeqProperPrefix) {
          unmatched78 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1554_left, _1557_right, _1545_format);
        }
      }
      if (unmatched78) {
        if (_source78.is_SeqPrefix) {
          unmatched78 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1554_left, _1557_right, _1545_format);
        }
      }
      if (unmatched78) {
        if (_source78.is_SetMerge) {
          unmatched78 = false;
          {
            r = ((_1554_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1557_right);
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_SetSubtraction) {
          unmatched78 = false;
          {
            r = ((_1554_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1557_right);
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_SetIntersection) {
          unmatched78 = false;
          {
            r = ((_1554_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1557_right);
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_Subset) {
          unmatched78 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1554_left, _1557_right, _1545_format);
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_ProperSubset) {
          unmatched78 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1554_left, _1557_right, _1545_format);
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_SetDisjoint) {
          unmatched78 = false;
          {
            r = ((_1554_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1557_right);
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_MapMerge) {
          unmatched78 = false;
          {
            r = ((_1554_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1557_right);
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_MapSubtraction) {
          unmatched78 = false;
          {
            r = ((_1554_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1557_right);
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_MultisetMerge) {
          unmatched78 = false;
          {
            r = ((_1554_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1557_right);
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_MultisetSubtraction) {
          unmatched78 = false;
          {
            r = ((_1554_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1557_right);
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_MultisetIntersection) {
          unmatched78 = false;
          {
            r = ((_1554_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1557_right);
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_Submultiset) {
          unmatched78 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1554_left, _1557_right, _1545_format);
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_ProperSubmultiset) {
          unmatched78 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1554_left, _1557_right, _1545_format);
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_MultisetDisjoint) {
          unmatched78 = false;
          {
            r = ((_1554_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1557_right);
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_Concat) {
          unmatched78 = false;
          {
            r = ((_1554_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1557_right);
          }
        }
      }
      if (unmatched78) {
        DAST._IBinOp _1560___v97 = _source78;
        unmatched78 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1542_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1542_op), _1554_left, _1557_right, _1545_format);
          } else {
            DAST._IBinOp _source79 = _1542_op;
            bool unmatched79 = true;
            if (unmatched79) {
              if (_source79.is_Eq) {
                bool _1561_referential = _source79.dtor_referential;
                bool _1562_nullable = _source79.dtor_nullable;
                unmatched79 = false;
                {
                  if (_1561_referential) {
                    if (_1562_nullable) {
                      r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1554_left, _1557_right));
                    } else {
                      r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1554_left, _1557_right));
                    }
                  } else {
                    if (((_1544_rExpr).is_SeqValue) && ((new BigInteger(((_1544_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1554_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1543_lExpr).is_SeqValue) && ((new BigInteger(((_1543_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1557_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1554_left, _1557_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
              }
            }
            if (unmatched79) {
              if (_source79.is_EuclidianDiv) {
                unmatched79 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1554_left, _1557_right));
                }
              }
            }
            if (unmatched79) {
              if (_source79.is_EuclidianMod) {
                unmatched79 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1554_left, _1557_right));
                }
              }
            }
            if (unmatched79) {
              Dafny.ISequence<Dafny.Rune> _1563_op = _source79.dtor_Passthrough_a0;
              unmatched79 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1563_op, _1554_left, _1557_right, _1545_format);
              }
            }
          }
        }
      }
      RAST._IExpr _out214;
      DCOMP._IOwnership _out215;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out214, out _out215);
      r = _out214;
      resultingOwnership = _out215;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1556_recIdentsL, _1559_recIdentsR);
      return ;
    }
    public void GenExprConvertFromNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs53 = e;
      DAST._IExpression _1564_expr = _let_tmp_rhs53.dtor_value;
      DAST._IType _1565_fromTpe = _let_tmp_rhs53.dtor_from;
      DAST._IType _1566_toTpe = _let_tmp_rhs53.dtor_typ;
      RAST._IExpr _1567_recursiveGen;
      DCOMP._IOwnership _1568_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1569_recIdents;
      RAST._IExpr _out216;
      DCOMP._IOwnership _out217;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out218;
      (this).GenExpr(_1564_expr, selfIdent, env, expectedOwnership, out _out216, out _out217, out _out218);
      _1567_recursiveGen = _out216;
      _1568_recOwned = _out217;
      _1569_recIdents = _out218;
      r = _1567_recursiveGen;
      if (object.Equals(_1568_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      RAST._IExpr _out219;
      DCOMP._IOwnership _out220;
      DCOMP.COMP.FromOwnership(r, _1568_recOwned, expectedOwnership, out _out219, out _out220);
      r = _out219;
      resultingOwnership = _out220;
      readIdents = _1569_recIdents;
    }
    public void GenExprConvertToNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IExpression _1570_expr = _let_tmp_rhs54.dtor_value;
      DAST._IType _1571_fromTpe = _let_tmp_rhs54.dtor_from;
      DAST._IType _1572_toTpe = _let_tmp_rhs54.dtor_typ;
      RAST._IExpr _1573_recursiveGen;
      DCOMP._IOwnership _1574_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1575_recIdents;
      RAST._IExpr _out221;
      DCOMP._IOwnership _out222;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out223;
      (this).GenExpr(_1570_expr, selfIdent, env, expectedOwnership, out _out221, out _out222, out _out223);
      _1573_recursiveGen = _out221;
      _1574_recOwned = _out222;
      _1575_recIdents = _out223;
      r = _1573_recursiveGen;
      if (object.Equals(_1574_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = (r).Clone();
      }
      r = ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
      RAST._IExpr _out224;
      DCOMP._IOwnership _out225;
      DCOMP.COMP.FromOwnership(r, _1574_recOwned, expectedOwnership, out _out224, out _out225);
      r = _out224;
      resultingOwnership = _out225;
      readIdents = _1575_recIdents;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _1576_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _1577_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _1578_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _1578_toTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1579___v98 = _let_tmp_rhs56.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _1580___v99 = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      DAST._IType _1581_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _1582_range = _let_tmp_rhs57.dtor_range;
      bool _1583_erase = _let_tmp_rhs57.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1584_attributes = _let_tmp_rhs57.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _1585_nativeToType;
      _1585_nativeToType = DCOMP.COMP.NewtypeToRustType(_1581_b, _1582_range);
      if (object.Equals(_1577_fromTpe, _1581_b)) {
        RAST._IExpr _1586_recursiveGen;
        DCOMP._IOwnership _1587_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1588_recIdents;
        RAST._IExpr _out226;
        DCOMP._IOwnership _out227;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out228;
        (this).GenExpr(_1576_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out226, out _out227, out _out228);
        _1586_recursiveGen = _out226;
        _1587_recOwned = _out227;
        _1588_recIdents = _out228;
        readIdents = _1588_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source80 = _1585_nativeToType;
        bool unmatched80 = true;
        if (unmatched80) {
          if (_source80.is_Some) {
            RAST._IType _1589_v = _source80.dtor_value;
            unmatched80 = false;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1586_recursiveGen, RAST.Expr.create_ExprFromType(_1589_v)));
            RAST._IExpr _out229;
            DCOMP._IOwnership _out230;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out229, out _out230);
            r = _out229;
            resultingOwnership = _out230;
          }
        }
        if (unmatched80) {
          unmatched80 = false;
          if (_1583_erase) {
            r = _1586_recursiveGen;
          } else {
            RAST._IType _1590_rhsType;
            RAST._IType _out231;
            _out231 = (this).GenType(_1578_toTpe, true, false);
            _1590_rhsType = _out231;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1590_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1586_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out232;
          DCOMP._IOwnership _out233;
          DCOMP.COMP.FromOwnership(r, _1587_recOwned, expectedOwnership, out _out232, out _out233);
          r = _out232;
          resultingOwnership = _out233;
        }
      } else {
        if ((_1585_nativeToType).is_Some) {
          DAST._IType _source81 = _1577_fromTpe;
          bool unmatched81 = true;
          if (unmatched81) {
            if (_source81.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1591___v100 = _source81.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _1592___v101 = _source81.dtor_typeArgs;
              DAST._IResolvedType resolved1 = _source81.dtor_resolved;
              if (resolved1.is_Newtype) {
                DAST._IType _1593_b0 = resolved1.dtor_baseType;
                DAST._INewtypeRange _1594_range0 = resolved1.dtor_range;
                bool _1595_erase0 = resolved1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1596_attributes0 = resolved1.dtor_attributes;
                unmatched81 = false;
                {
                  Std.Wrappers._IOption<RAST._IType> _1597_nativeFromType;
                  _1597_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1593_b0, _1594_range0);
                  if ((_1597_nativeFromType).is_Some) {
                    RAST._IExpr _1598_recursiveGen;
                    DCOMP._IOwnership _1599_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1600_recIdents;
                    RAST._IExpr _out234;
                    DCOMP._IOwnership _out235;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out236;
                    (this).GenExpr(_1576_expr, selfIdent, env, expectedOwnership, out _out234, out _out235, out _out236);
                    _1598_recursiveGen = _out234;
                    _1599_recOwned = _out235;
                    _1600_recIdents = _out236;
                    RAST._IExpr _out237;
                    DCOMP._IOwnership _out238;
                    DCOMP.COMP.FromOwnership(RAST.Expr.create_TypeAscription(_1598_recursiveGen, (_1585_nativeToType).dtor_value), _1599_recOwned, expectedOwnership, out _out237, out _out238);
                    r = _out237;
                    resultingOwnership = _out238;
                    readIdents = _1600_recIdents;
                    return ;
                  }
                }
              }
            }
          }
          if (unmatched81) {
            DAST._IType _1601___v102 = _source81;
            unmatched81 = false;
          }
          if (object.Equals(_1577_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1602_recursiveGen;
            DCOMP._IOwnership _1603_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1604_recIdents;
            RAST._IExpr _out239;
            DCOMP._IOwnership _out240;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out241;
            (this).GenExpr(_1576_expr, selfIdent, env, expectedOwnership, out _out239, out _out240, out _out241);
            _1602_recursiveGen = _out239;
            _1603_recOwned = _out240;
            _1604_recIdents = _out241;
            RAST._IExpr _out242;
            DCOMP._IOwnership _out243;
            DCOMP.COMP.FromOwnership(RAST.Expr.create_TypeAscription((_1602_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1585_nativeToType).dtor_value), _1603_recOwned, expectedOwnership, out _out242, out _out243);
            r = _out242;
            resultingOwnership = _out243;
            readIdents = _1604_recIdents;
            return ;
          }
        }
        RAST._IExpr _out244;
        DCOMP._IOwnership _out245;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out246;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1576_expr, _1577_fromTpe, _1581_b), _1581_b, _1578_toTpe), selfIdent, env, expectedOwnership, out _out244, out _out245, out _out246);
        r = _out244;
        resultingOwnership = _out245;
        readIdents = _out246;
      }
    }
    public void GenExprConvertFromNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs58 = e;
      DAST._IExpression _1605_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _1606_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _1607_toTpe = _let_tmp_rhs58.dtor_typ;
      DAST._IType _let_tmp_rhs59 = _1606_fromTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1608___v103 = _let_tmp_rhs59.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _1609___v104 = _let_tmp_rhs59.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs60 = _let_tmp_rhs59.dtor_resolved;
      DAST._IType _1610_b = _let_tmp_rhs60.dtor_baseType;
      DAST._INewtypeRange _1611_range = _let_tmp_rhs60.dtor_range;
      bool _1612_erase = _let_tmp_rhs60.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1613_attributes = _let_tmp_rhs60.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _1614_nativeFromType;
      _1614_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1610_b, _1611_range);
      if (object.Equals(_1610_b, _1607_toTpe)) {
        RAST._IExpr _1615_recursiveGen;
        DCOMP._IOwnership _1616_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1617_recIdents;
        RAST._IExpr _out247;
        DCOMP._IOwnership _out248;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out249;
        (this).GenExpr(_1605_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out247, out _out248, out _out249);
        _1615_recursiveGen = _out247;
        _1616_recOwned = _out248;
        _1617_recIdents = _out249;
        readIdents = _1617_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source82 = _1614_nativeFromType;
        bool unmatched82 = true;
        if (unmatched82) {
          if (_source82.is_Some) {
            RAST._IType _1618_v = _source82.dtor_value;
            unmatched82 = false;
            RAST._IType _1619_toTpeRust;
            RAST._IType _out250;
            _out250 = (this).GenType(_1607_toTpe, false, false);
            _1619_toTpeRust = _out250;
            r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1619_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1615_recursiveGen));
            RAST._IExpr _out251;
            DCOMP._IOwnership _out252;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out251, out _out252);
            r = _out251;
            resultingOwnership = _out252;
          }
        }
        if (unmatched82) {
          unmatched82 = false;
          if (_1612_erase) {
            r = _1615_recursiveGen;
          } else {
            r = (_1615_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out253;
          DCOMP._IOwnership _out254;
          DCOMP.COMP.FromOwnership(r, _1616_recOwned, expectedOwnership, out _out253, out _out254);
          r = _out253;
          resultingOwnership = _out254;
        }
      } else {
        if ((_1614_nativeFromType).is_Some) {
          if (object.Equals(_1607_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1620_recursiveGen;
            DCOMP._IOwnership _1621_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1622_recIdents;
            RAST._IExpr _out255;
            DCOMP._IOwnership _out256;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out257;
            (this).GenExpr(_1605_expr, selfIdent, env, expectedOwnership, out _out255, out _out256, out _out257);
            _1620_recursiveGen = _out255;
            _1621_recOwned = _out256;
            _1622_recIdents = _out257;
            RAST._IExpr _out258;
            DCOMP._IOwnership _out259;
            DCOMP.COMP.FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1620_recursiveGen, (this).DafnyCharUnderlying)), _1621_recOwned, expectedOwnership, out _out258, out _out259);
            r = _out258;
            resultingOwnership = _out259;
            readIdents = _1622_recIdents;
            return ;
          }
        }
        RAST._IExpr _out260;
        DCOMP._IOwnership _out261;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out262;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1605_expr, _1606_fromTpe, _1610_b), _1610_b, _1607_toTpe), selfIdent, env, expectedOwnership, out _out260, out _out261, out _out262);
        r = _out260;
        resultingOwnership = _out261;
        readIdents = _out262;
      }
    }
    public void GenExprConvertNotImplemented(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs61 = e;
      DAST._IExpression _1623_expr = _let_tmp_rhs61.dtor_value;
      DAST._IType _1624_fromTpe = _let_tmp_rhs61.dtor_from;
      DAST._IType _1625_toTpe = _let_tmp_rhs61.dtor_typ;
      RAST._IType _1626_fromTpeGen;
      RAST._IType _out263;
      _out263 = (this).GenType(_1624_fromTpe, true, false);
      _1626_fromTpeGen = _out263;
      RAST._IType _1627_toTpeGen;
      RAST._IType _out264;
      _out264 = (this).GenType(_1625_toTpe, true, false);
      _1627_toTpeGen = _out264;
      RAST._IExpr _1628_recursiveGen;
      DCOMP._IOwnership _1629_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1630_recIdents;
      RAST._IExpr _out265;
      DCOMP._IOwnership _out266;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out267;
      (this).GenExpr(_1623_expr, selfIdent, env, expectedOwnership, out _out265, out _out266, out _out267);
      _1628_recursiveGen = _out265;
      _1629_recOwned = _out266;
      _1630_recIdents = _out267;
      readIdents = _1630_recIdents;
      if (RAST.__default.IsUpcastConversion(_1626_fromTpeGen, _1627_toTpeGen)) {
        RAST._IExpr _out268;
        DCOMP._IOwnership _out269;
        DCOMP.COMP.FromOwnership(_1628_recursiveGen, _1629_recOwned, DCOMP.Ownership.create_OwnershipOwned(), out _out268, out _out269);
        r = _out268;
        resultingOwnership = _out269;
        r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("UpcastTo"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1627_toTpeGen))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast_to"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1628_recursiveGen));
        RAST._IExpr _out270;
        DCOMP._IOwnership _out271;
        DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out270, out _out271);
        r = _out270;
        resultingOwnership = _out271;
      } else {
        Dafny.ISequence<Dafny.Rune> _1631_msg;
        _1631_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1626_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1627_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1631_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1628_recursiveGen)._ToString(DCOMP.__default.IND), _1631_msg));
        RAST._IExpr _out272;
        DCOMP._IOwnership _out273;
        DCOMP.COMP.FromOwnership(r, _1629_recOwned, expectedOwnership, out _out272, out _out273);
        r = _out272;
        resultingOwnership = _out273;
      }
    }
    public void GenExprConvert(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs62 = e;
      DAST._IExpression _1632_expr = _let_tmp_rhs62.dtor_value;
      DAST._IType _1633_fromTpe = _let_tmp_rhs62.dtor_from;
      DAST._IType _1634_toTpe = _let_tmp_rhs62.dtor_typ;
      if (object.Equals(_1633_fromTpe, _1634_toTpe)) {
        RAST._IExpr _1635_recursiveGen;
        DCOMP._IOwnership _1636_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1637_recIdents;
        RAST._IExpr _out274;
        DCOMP._IOwnership _out275;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out276;
        (this).GenExpr(_1632_expr, selfIdent, env, expectedOwnership, out _out274, out _out275, out _out276);
        _1635_recursiveGen = _out274;
        _1636_recOwned = _out275;
        _1637_recIdents = _out276;
        r = _1635_recursiveGen;
        RAST._IExpr _out277;
        DCOMP._IOwnership _out278;
        DCOMP.COMP.FromOwnership(r, _1636_recOwned, expectedOwnership, out _out277, out _out278);
        r = _out277;
        resultingOwnership = _out278;
        readIdents = _1637_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source83 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1633_fromTpe, _1634_toTpe);
        bool unmatched83 = true;
        if (unmatched83) {
          DAST._IType _02 = _source83.dtor__0;
          if (_02.is_Nullable) {
            DAST._IType _1638___v105 = _02.dtor_Nullable_a0;
            DAST._IType _1639___v106 = _source83.dtor__1;
            unmatched83 = false;
            {
              RAST._IExpr _out279;
              DCOMP._IOwnership _out280;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out281;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out279, out _out280, out _out281);
              r = _out279;
              resultingOwnership = _out280;
              readIdents = _out281;
            }
          }
        }
        if (unmatched83) {
          DAST._IType _1640___v107 = _source83.dtor__0;
          DAST._IType _12 = _source83.dtor__1;
          if (_12.is_Nullable) {
            DAST._IType _1641___v108 = _12.dtor_Nullable_a0;
            unmatched83 = false;
            {
              RAST._IExpr _out282;
              DCOMP._IOwnership _out283;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out284;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out282, out _out283, out _out284);
              r = _out282;
              resultingOwnership = _out283;
              readIdents = _out284;
            }
          }
        }
        if (unmatched83) {
          DAST._IType _1642___v109 = _source83.dtor__0;
          DAST._IType _13 = _source83.dtor__1;
          if (_13.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1643___v110 = _13.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1644___v111 = _13.dtor_typeArgs;
            DAST._IResolvedType resolved2 = _13.dtor_resolved;
            if (resolved2.is_Newtype) {
              DAST._IType _1645_b = resolved2.dtor_baseType;
              DAST._INewtypeRange _1646_range = resolved2.dtor_range;
              bool _1647_erase = resolved2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1648_attributes = resolved2.dtor_attributes;
              unmatched83 = false;
              {
                RAST._IExpr _out285;
                DCOMP._IOwnership _out286;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out287;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out285, out _out286, out _out287);
                r = _out285;
                resultingOwnership = _out286;
                readIdents = _out287;
              }
            }
          }
        }
        if (unmatched83) {
          DAST._IType _03 = _source83.dtor__0;
          if (_03.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1649___v112 = _03.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1650___v113 = _03.dtor_typeArgs;
            DAST._IResolvedType resolved3 = _03.dtor_resolved;
            if (resolved3.is_Newtype) {
              DAST._IType _1651_b = resolved3.dtor_baseType;
              DAST._INewtypeRange _1652_range = resolved3.dtor_range;
              bool _1653_erase = resolved3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1654_attributes = resolved3.dtor_attributes;
              DAST._IType _1655___v114 = _source83.dtor__1;
              unmatched83 = false;
              {
                RAST._IExpr _out288;
                DCOMP._IOwnership _out289;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out290;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out288, out _out289, out _out290);
                r = _out288;
                resultingOwnership = _out289;
                readIdents = _out290;
              }
            }
          }
        }
        if (unmatched83) {
          DAST._IType _04 = _source83.dtor__0;
          if (_04.is_Primitive) {
            DAST._IPrimitive _h92 = _04.dtor_Primitive_a0;
            if (_h92.is_Int) {
              DAST._IType _14 = _source83.dtor__1;
              if (_14.is_Primitive) {
                DAST._IPrimitive _h93 = _14.dtor_Primitive_a0;
                if (_h93.is_Real) {
                  unmatched83 = false;
                  {
                    RAST._IExpr _1656_recursiveGen;
                    DCOMP._IOwnership _1657___v115;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1658_recIdents;
                    RAST._IExpr _out291;
                    DCOMP._IOwnership _out292;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out293;
                    (this).GenExpr(_1632_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out291, out _out292, out _out293);
                    _1656_recursiveGen = _out291;
                    _1657___v115 = _out292;
                    _1658_recIdents = _out293;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1656_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out294;
                    DCOMP._IOwnership _out295;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out294, out _out295);
                    r = _out294;
                    resultingOwnership = _out295;
                    readIdents = _1658_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched83) {
          DAST._IType _05 = _source83.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h94 = _05.dtor_Primitive_a0;
            if (_h94.is_Real) {
              DAST._IType _15 = _source83.dtor__1;
              if (_15.is_Primitive) {
                DAST._IPrimitive _h95 = _15.dtor_Primitive_a0;
                if (_h95.is_Int) {
                  unmatched83 = false;
                  {
                    RAST._IExpr _1659_recursiveGen;
                    DCOMP._IOwnership _1660___v116;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1661_recIdents;
                    RAST._IExpr _out296;
                    DCOMP._IOwnership _out297;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out298;
                    (this).GenExpr(_1632_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out296, out _out297, out _out298);
                    _1659_recursiveGen = _out296;
                    _1660___v116 = _out297;
                    _1661_recIdents = _out298;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1659_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out299;
                    DCOMP._IOwnership _out300;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out299, out _out300);
                    r = _out299;
                    resultingOwnership = _out300;
                    readIdents = _1661_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched83) {
          DAST._IType _06 = _source83.dtor__0;
          if (_06.is_Primitive) {
            DAST._IPrimitive _h96 = _06.dtor_Primitive_a0;
            if (_h96.is_Int) {
              DAST._IType _16 = _source83.dtor__1;
              if (_16.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1662___v117 = _16.dtor_Passthrough_a0;
                unmatched83 = false;
                {
                  RAST._IType _1663_rhsType;
                  RAST._IType _out301;
                  _out301 = (this).GenType(_1634_toTpe, true, false);
                  _1663_rhsType = _out301;
                  RAST._IExpr _1664_recursiveGen;
                  DCOMP._IOwnership _1665___v118;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1666_recIdents;
                  RAST._IExpr _out302;
                  DCOMP._IOwnership _out303;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out304;
                  (this).GenExpr(_1632_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out302, out _out303, out _out304);
                  _1664_recursiveGen = _out302;
                  _1665___v118 = _out303;
                  _1666_recIdents = _out304;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1663_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1664_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out305;
                  DCOMP._IOwnership _out306;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out305, out _out306);
                  r = _out305;
                  resultingOwnership = _out306;
                  readIdents = _1666_recIdents;
                }
              }
            }
          }
        }
        if (unmatched83) {
          DAST._IType _07 = _source83.dtor__0;
          if (_07.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1667___v119 = _07.dtor_Passthrough_a0;
            DAST._IType _17 = _source83.dtor__1;
            if (_17.is_Primitive) {
              DAST._IPrimitive _h97 = _17.dtor_Primitive_a0;
              if (_h97.is_Int) {
                unmatched83 = false;
                {
                  RAST._IType _1668_rhsType;
                  RAST._IType _out307;
                  _out307 = (this).GenType(_1633_fromTpe, true, false);
                  _1668_rhsType = _out307;
                  RAST._IExpr _1669_recursiveGen;
                  DCOMP._IOwnership _1670___v120;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1671_recIdents;
                  RAST._IExpr _out308;
                  DCOMP._IOwnership _out309;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out310;
                  (this).GenExpr(_1632_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out308, out _out309, out _out310);
                  _1669_recursiveGen = _out308;
                  _1670___v120 = _out309;
                  _1671_recIdents = _out310;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::dafny_runtime::BigInt::from("), (_1669_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")}")));
                  RAST._IExpr _out311;
                  DCOMP._IOwnership _out312;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out311, out _out312);
                  r = _out311;
                  resultingOwnership = _out312;
                  readIdents = _1671_recIdents;
                }
              }
            }
          }
        }
        if (unmatched83) {
          DAST._IType _08 = _source83.dtor__0;
          if (_08.is_Primitive) {
            DAST._IPrimitive _h98 = _08.dtor_Primitive_a0;
            if (_h98.is_Int) {
              DAST._IType _18 = _source83.dtor__1;
              if (_18.is_Primitive) {
                DAST._IPrimitive _h99 = _18.dtor_Primitive_a0;
                if (_h99.is_Char) {
                  unmatched83 = false;
                  {
                    RAST._IType _1672_rhsType;
                    RAST._IType _out313;
                    _out313 = (this).GenType(_1634_toTpe, true, false);
                    _1672_rhsType = _out313;
                    RAST._IExpr _1673_recursiveGen;
                    DCOMP._IOwnership _1674___v121;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1675_recIdents;
                    RAST._IExpr _out314;
                    DCOMP._IOwnership _out315;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out316;
                    (this).GenExpr(_1632_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out314, out _out315, out _out316);
                    _1673_recursiveGen = _out314;
                    _1674___v121 = _out315;
                    _1675_recIdents = _out316;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), (_1673_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()")));
                    RAST._IExpr _out317;
                    DCOMP._IOwnership _out318;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out317, out _out318);
                    r = _out317;
                    resultingOwnership = _out318;
                    readIdents = _1675_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched83) {
          DAST._IType _09 = _source83.dtor__0;
          if (_09.is_Primitive) {
            DAST._IPrimitive _h910 = _09.dtor_Primitive_a0;
            if (_h910.is_Char) {
              DAST._IType _19 = _source83.dtor__1;
              if (_19.is_Primitive) {
                DAST._IPrimitive _h911 = _19.dtor_Primitive_a0;
                if (_h911.is_Int) {
                  unmatched83 = false;
                  {
                    RAST._IType _1676_rhsType;
                    RAST._IType _out319;
                    _out319 = (this).GenType(_1633_fromTpe, true, false);
                    _1676_rhsType = _out319;
                    RAST._IExpr _1677_recursiveGen;
                    DCOMP._IOwnership _1678___v122;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1679_recIdents;
                    RAST._IExpr _out320;
                    DCOMP._IOwnership _out321;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out322;
                    (this).GenExpr(_1632_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out320, out _out321, out _out322);
                    _1677_recursiveGen = _out320;
                    _1678___v122 = _out321;
                    _1679_recIdents = _out322;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1677_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out323;
                    DCOMP._IOwnership _out324;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out323, out _out324);
                    r = _out323;
                    resultingOwnership = _out324;
                    readIdents = _1679_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched83) {
          DAST._IType _010 = _source83.dtor__0;
          if (_010.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1680___v123 = _010.dtor_Passthrough_a0;
            DAST._IType _110 = _source83.dtor__1;
            if (_110.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1681___v124 = _110.dtor_Passthrough_a0;
              unmatched83 = false;
              {
                RAST._IExpr _1682_recursiveGen;
                DCOMP._IOwnership _1683___v125;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1684_recIdents;
                RAST._IExpr _out325;
                DCOMP._IOwnership _out326;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out327;
                (this).GenExpr(_1632_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out325, out _out326, out _out327);
                _1682_recursiveGen = _out325;
                _1683___v125 = _out326;
                _1684_recIdents = _out327;
                RAST._IType _1685_toTpeGen;
                RAST._IType _out328;
                _out328 = (this).GenType(_1634_toTpe, true, false);
                _1685_toTpeGen = _out328;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1682_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1685_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out329;
                DCOMP._IOwnership _out330;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out329, out _out330);
                r = _out329;
                resultingOwnership = _out330;
                readIdents = _1684_recIdents;
              }
            }
          }
        }
        if (unmatched83) {
          _System._ITuple2<DAST._IType, DAST._IType> _1686___v126 = _source83;
          unmatched83 = false;
          {
            RAST._IExpr _out331;
            DCOMP._IOwnership _out332;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out333;
            (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out331, out _out332, out _out333);
            r = _out331;
            resultingOwnership = _out332;
            readIdents = _out333;
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
      Std.Wrappers._IOption<RAST._IType> _1687_tpe;
      _1687_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1688_placeboOpt;
      _1688_placeboOpt = (((_1687_tpe).is_Some) ? (((_1687_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _1689_currentlyBorrowed;
      _1689_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1690_noNeedOfClone;
      _1690_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1688_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _1689_currentlyBorrowed = false;
        _1690_noNeedOfClone = true;
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = ((_1689_currentlyBorrowed) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()));
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if (((_1687_tpe).is_Some) && (((_1687_tpe).dtor_value).IsObjectOrPointer())) {
          if (((_1687_tpe).dtor_value).IsObject()) {
            r = (r).Clone();
          }
          r = ((this).modify__macro).Apply1(r);
        } else {
          r = RAST.__default.BorrowMut(r);
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        if (!(_1690_noNeedOfClone)) {
          r = (r).Clone();
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1690_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1689_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (((_1687_tpe).is_Some) && (((_1687_tpe).dtor_value).IsPointer())) {
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
      DAST._IExpression _source84 = e;
      bool unmatched84 = true;
      if (unmatched84) {
        if (_source84.is_Literal) {
          DAST._ILiteral _1691___v127 = _source84.dtor_Literal_a0;
          unmatched84 = false;
          RAST._IExpr _out334;
          DCOMP._IOwnership _out335;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out336;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out334, out _out335, out _out336);
          r = _out334;
          resultingOwnership = _out335;
          readIdents = _out336;
        }
      }
      if (unmatched84) {
        if (_source84.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1692_name = _source84.dtor_Ident_a0;
          unmatched84 = false;
          {
            RAST._IExpr _out337;
            DCOMP._IOwnership _out338;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out339;
            (this).GenIdent(DCOMP.__default.escapeName(_1692_name), selfIdent, env, expectedOwnership, out _out337, out _out338, out _out339);
            r = _out337;
            resultingOwnership = _out338;
            readIdents = _out339;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1693_path = _source84.dtor_Companion_a0;
          unmatched84 = false;
          {
            RAST._IExpr _out340;
            _out340 = DCOMP.COMP.GenPathExpr(_1693_path);
            r = _out340;
            if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else {
              RAST._IExpr _out341;
              DCOMP._IOwnership _out342;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out341, out _out342);
              r = _out341;
              resultingOwnership = _out342;
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_InitializationValue) {
          DAST._IType _1694_typ = _source84.dtor_typ;
          unmatched84 = false;
          {
            RAST._IType _1695_typExpr;
            RAST._IType _out343;
            _out343 = (this).GenType(_1694_typ, false, false);
            _1695_typExpr = _out343;
            if ((_1695_typExpr).IsObjectOrPointer()) {
              r = (_1695_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1695_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
            }
            RAST._IExpr _out344;
            DCOMP._IOwnership _out345;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out344, out _out345);
            r = _out344;
            resultingOwnership = _out345;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _1696_values = _source84.dtor_Tuple_a0;
          unmatched84 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1697_exprs;
            _1697_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi33 = new BigInteger((_1696_values).Count);
            for (BigInteger _1698_i = BigInteger.Zero; _1698_i < _hi33; _1698_i++) {
              RAST._IExpr _1699_recursiveGen;
              DCOMP._IOwnership _1700___v128;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1701_recIdents;
              RAST._IExpr _out346;
              DCOMP._IOwnership _out347;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out348;
              (this).GenExpr((_1696_values).Select(_1698_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out346, out _out347, out _out348);
              _1699_recursiveGen = _out346;
              _1700___v128 = _out347;
              _1701_recIdents = _out348;
              _1697_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1697_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1699_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1701_recIdents);
            }
            r = (((new BigInteger((_1696_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_1697_exprs)) : (RAST.__default.SystemTuple(_1697_exprs)));
            RAST._IExpr _out349;
            DCOMP._IOwnership _out350;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out349, out _out350);
            r = _out349;
            resultingOwnership = _out350;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1702_path = _source84.dtor_path;
          Dafny.ISequence<DAST._IType> _1703_typeArgs = _source84.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1704_args = _source84.dtor_args;
          unmatched84 = false;
          {
            RAST._IExpr _out351;
            _out351 = DCOMP.COMP.GenPathExpr(_1702_path);
            r = _out351;
            if ((new BigInteger((_1703_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1705_typeExprs;
              _1705_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi34 = new BigInteger((_1703_typeArgs).Count);
              for (BigInteger _1706_i = BigInteger.Zero; _1706_i < _hi34; _1706_i++) {
                RAST._IType _1707_typeExpr;
                RAST._IType _out352;
                _out352 = (this).GenType((_1703_typeArgs).Select(_1706_i), false, false);
                _1707_typeExpr = _out352;
                _1705_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1705_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1707_typeExpr));
              }
              r = (r).ApplyType(_1705_typeExprs);
            }
            r = (r).MSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1708_arguments;
            _1708_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi35 = new BigInteger((_1704_args).Count);
            for (BigInteger _1709_i = BigInteger.Zero; _1709_i < _hi35; _1709_i++) {
              RAST._IExpr _1710_recursiveGen;
              DCOMP._IOwnership _1711___v129;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1712_recIdents;
              RAST._IExpr _out353;
              DCOMP._IOwnership _out354;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out355;
              (this).GenExpr((_1704_args).Select(_1709_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out353, out _out354, out _out355);
              _1710_recursiveGen = _out353;
              _1711___v129 = _out354;
              _1712_recIdents = _out355;
              _1708_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1708_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1710_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1712_recIdents);
            }
            r = (r).Apply(_1708_arguments);
            RAST._IExpr _out356;
            DCOMP._IOwnership _out357;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out356, out _out357);
            r = _out356;
            resultingOwnership = _out357;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_NewUninitArray) {
          Dafny.ISequence<DAST._IExpression> _1713_dims = _source84.dtor_dims;
          DAST._IType _1714_typ = _source84.dtor_typ;
          unmatched84 = false;
          {
            if ((new BigInteger(16)) < (new BigInteger((_1713_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _1715_msg;
              _1715_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1715_msg);
              }
              r = RAST.Expr.create_RawExpr(_1715_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _1716_typeGen;
              RAST._IType _out358;
              _out358 = (this).GenType(_1714_typ, false, false);
              _1716_typeGen = _out358;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _1717_dimExprs;
              _1717_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi36 = new BigInteger((_1713_dims).Count);
              for (BigInteger _1718_i = BigInteger.Zero; _1718_i < _hi36; _1718_i++) {
                RAST._IExpr _1719_recursiveGen;
                DCOMP._IOwnership _1720___v130;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1721_recIdents;
                RAST._IExpr _out359;
                DCOMP._IOwnership _out360;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out361;
                (this).GenExpr((_1713_dims).Select(_1718_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out359, out _out360, out _out361);
                _1719_recursiveGen = _out359;
                _1720___v130 = _out360;
                _1721_recIdents = _out361;
                _1717_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1717_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(((_1719_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_usize"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1721_recIdents);
              }
              if ((new BigInteger((_1713_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _1722_class__name;
                _1722_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_1713_dims).Count)));
                r = ((((RAST.__default.dafny__runtime).MSel(_1722_class__name)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1716_typeGen))).MSel((this).placebos__usize)).Apply(_1717_dimExprs);
              } else {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1716_typeGen))).Apply(_1717_dimExprs);
              }
            }
            RAST._IExpr _out362;
            DCOMP._IOwnership _out363;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out362, out _out363);
            r = _out362;
            resultingOwnership = _out363;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_ArrayIndexToInt) {
          DAST._IExpression _1723_underlying = _source84.dtor_value;
          unmatched84 = false;
          {
            RAST._IExpr _1724_recursiveGen;
            DCOMP._IOwnership _1725___v131;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1726_recIdents;
            RAST._IExpr _out364;
            DCOMP._IOwnership _out365;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out366;
            (this).GenExpr(_1723_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out364, out _out365, out _out366);
            _1724_recursiveGen = _out364;
            _1725___v131 = _out365;
            _1726_recIdents = _out366;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(_1724_recursiveGen);
            readIdents = _1726_recIdents;
            RAST._IExpr _out367;
            DCOMP._IOwnership _out368;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out367, out _out368);
            r = _out367;
            resultingOwnership = _out368;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_FinalizeNewArray) {
          DAST._IExpression _1727_underlying = _source84.dtor_value;
          DAST._IType _1728_typ = _source84.dtor_typ;
          unmatched84 = false;
          {
            RAST._IType _1729_tpe;
            RAST._IType _out369;
            _out369 = (this).GenType(_1728_typ, false, false);
            _1729_tpe = _out369;
            RAST._IExpr _1730_recursiveGen;
            DCOMP._IOwnership _1731___v132;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1732_recIdents;
            RAST._IExpr _out370;
            DCOMP._IOwnership _out371;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out372;
            (this).GenExpr(_1727_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out370, out _out371, out _out372);
            _1730_recursiveGen = _out370;
            _1731___v132 = _out371;
            _1732_recIdents = _out372;
            readIdents = _1732_recIdents;
            if ((_1729_tpe).IsObjectOrPointer()) {
              RAST._IType _1733_t;
              _1733_t = (_1729_tpe).ObjectOrPointerUnderlying();
              if ((_1733_t).is_Array) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).array__construct)).Apply1(_1730_recursiveGen);
              } else if ((_1733_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _1734_c;
                _1734_c = (_1733_t).MultiArrayClass();
                r = (((RAST.__default.dafny__runtime).MSel(_1734_c)).MSel((this).array__construct)).Apply1(_1730_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_1729_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_1729_tpe)._ToString(DCOMP.__default.IND)));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            }
            RAST._IExpr _out373;
            DCOMP._IOwnership _out374;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out373, out _out374);
            r = _out373;
            resultingOwnership = _out374;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_DatatypeValue) {
          DAST._IDatatypeType _1735_datatypeType = _source84.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1736_typeArgs = _source84.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1737_variant = _source84.dtor_variant;
          bool _1738_isCo = _source84.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1739_values = _source84.dtor_contents;
          unmatched84 = false;
          {
            RAST._IExpr _out375;
            _out375 = DCOMP.COMP.GenPathExpr((_1735_datatypeType).dtor_path);
            r = _out375;
            Dafny.ISequence<RAST._IType> _1740_genTypeArgs;
            _1740_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi37 = new BigInteger((_1736_typeArgs).Count);
            for (BigInteger _1741_i = BigInteger.Zero; _1741_i < _hi37; _1741_i++) {
              RAST._IType _1742_typeExpr;
              RAST._IType _out376;
              _out376 = (this).GenType((_1736_typeArgs).Select(_1741_i), false, false);
              _1742_typeExpr = _out376;
              _1740_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1740_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1742_typeExpr));
            }
            if ((new BigInteger((_1736_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1740_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1737_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1743_assignments;
            _1743_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi38 = new BigInteger((_1739_values).Count);
            for (BigInteger _1744_i = BigInteger.Zero; _1744_i < _hi38; _1744_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs63 = (_1739_values).Select(_1744_i);
              Dafny.ISequence<Dafny.Rune> _1745_name = _let_tmp_rhs63.dtor__0;
              DAST._IExpression _1746_value = _let_tmp_rhs63.dtor__1;
              if (_1738_isCo) {
                RAST._IExpr _1747_recursiveGen;
                DCOMP._IOwnership _1748___v133;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1749_recIdents;
                RAST._IExpr _out377;
                DCOMP._IOwnership _out378;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out379;
                (this).GenExpr(_1746_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out377, out _out378, out _out379);
                _1747_recursiveGen = _out377;
                _1748___v133 = _out378;
                _1749_recIdents = _out379;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1749_recIdents);
                Dafny.ISequence<Dafny.Rune> _1750_allReadCloned;
                _1750_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1749_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1751_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1749_recIdents).Elements) {
                    _1751_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1749_recIdents).Contains(_1751_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 3796)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1750_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1750_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1751_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1751_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1749_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1749_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1751_next));
                }
                Dafny.ISequence<Dafny.Rune> _1752_wasAssigned;
                _1752_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1750_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1747_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1743_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1743_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1745_name), RAST.Expr.create_RawExpr(_1752_wasAssigned))));
              } else {
                RAST._IExpr _1753_recursiveGen;
                DCOMP._IOwnership _1754___v134;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1755_recIdents;
                RAST._IExpr _out380;
                DCOMP._IOwnership _out381;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out382;
                (this).GenExpr(_1746_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out380, out _out381, out _out382);
                _1753_recursiveGen = _out380;
                _1754___v134 = _out381;
                _1755_recIdents = _out382;
                _1743_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1743_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1745_name), _1753_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1755_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1743_assignments);
            if ((this).IsRcWrapped((_1735_datatypeType).dtor_attributes)) {
              r = RAST.__default.RcNew(r);
            }
            RAST._IExpr _out383;
            DCOMP._IOwnership _out384;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out383, out _out384);
            r = _out383;
            resultingOwnership = _out384;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_Convert) {
          DAST._IExpression _1756___v135 = _source84.dtor_value;
          DAST._IType _1757___v136 = _source84.dtor_from;
          DAST._IType _1758___v137 = _source84.dtor_typ;
          unmatched84 = false;
          {
            RAST._IExpr _out385;
            DCOMP._IOwnership _out386;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out387;
            (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out385, out _out386, out _out387);
            r = _out385;
            resultingOwnership = _out386;
            readIdents = _out387;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_SeqConstruct) {
          DAST._IExpression _1759_length = _source84.dtor_length;
          DAST._IExpression _1760_expr = _source84.dtor_elem;
          unmatched84 = false;
          {
            RAST._IExpr _1761_recursiveGen;
            DCOMP._IOwnership _1762___v138;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1763_recIdents;
            RAST._IExpr _out388;
            DCOMP._IOwnership _out389;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out390;
            (this).GenExpr(_1760_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out388, out _out389, out _out390);
            _1761_recursiveGen = _out388;
            _1762___v138 = _out389;
            _1763_recIdents = _out390;
            RAST._IExpr _1764_lengthGen;
            DCOMP._IOwnership _1765___v139;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1766_lengthIdents;
            RAST._IExpr _out391;
            DCOMP._IOwnership _out392;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out393;
            (this).GenExpr(_1759_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out391, out _out392, out _out393);
            _1764_lengthGen = _out391;
            _1765___v139 = _out392;
            _1766_lengthIdents = _out393;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1761_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1764_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1763_recIdents, _1766_lengthIdents);
            RAST._IExpr _out394;
            DCOMP._IOwnership _out395;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out394, out _out395);
            r = _out394;
            resultingOwnership = _out395;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _1767_exprs = _source84.dtor_elements;
          DAST._IType _1768_typ = _source84.dtor_typ;
          unmatched84 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1769_genTpe;
            RAST._IType _out396;
            _out396 = (this).GenType(_1768_typ, false, false);
            _1769_genTpe = _out396;
            BigInteger _1770_i;
            _1770_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1771_args;
            _1771_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1770_i) < (new BigInteger((_1767_exprs).Count))) {
              RAST._IExpr _1772_recursiveGen;
              DCOMP._IOwnership _1773___v140;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1774_recIdents;
              RAST._IExpr _out397;
              DCOMP._IOwnership _out398;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out399;
              (this).GenExpr((_1767_exprs).Select(_1770_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out397, out _out398, out _out399);
              _1772_recursiveGen = _out397;
              _1773___v140 = _out398;
              _1774_recIdents = _out399;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1774_recIdents);
              _1771_args = Dafny.Sequence<RAST._IExpr>.Concat(_1771_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1772_recursiveGen));
              _1770_i = (_1770_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_1771_args);
            if ((new BigInteger((_1771_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1769_genTpe));
            }
            RAST._IExpr _out400;
            DCOMP._IOwnership _out401;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out400, out _out401);
            r = _out400;
            resultingOwnership = _out401;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _1775_exprs = _source84.dtor_elements;
          unmatched84 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1776_generatedValues;
            _1776_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1777_i;
            _1777_i = BigInteger.Zero;
            while ((_1777_i) < (new BigInteger((_1775_exprs).Count))) {
              RAST._IExpr _1778_recursiveGen;
              DCOMP._IOwnership _1779___v141;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1780_recIdents;
              RAST._IExpr _out402;
              DCOMP._IOwnership _out403;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out404;
              (this).GenExpr((_1775_exprs).Select(_1777_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out402, out _out403, out _out404);
              _1778_recursiveGen = _out402;
              _1779___v141 = _out403;
              _1780_recIdents = _out404;
              _1776_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1776_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1778_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1780_recIdents);
              _1777_i = (_1777_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_1776_generatedValues);
            RAST._IExpr _out405;
            DCOMP._IOwnership _out406;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out405, out _out406);
            r = _out405;
            resultingOwnership = _out406;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _1781_exprs = _source84.dtor_elements;
          unmatched84 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1782_generatedValues;
            _1782_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1783_i;
            _1783_i = BigInteger.Zero;
            while ((_1783_i) < (new BigInteger((_1781_exprs).Count))) {
              RAST._IExpr _1784_recursiveGen;
              DCOMP._IOwnership _1785___v142;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1786_recIdents;
              RAST._IExpr _out407;
              DCOMP._IOwnership _out408;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
              (this).GenExpr((_1781_exprs).Select(_1783_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out407, out _out408, out _out409);
              _1784_recursiveGen = _out407;
              _1785___v142 = _out408;
              _1786_recIdents = _out409;
              _1782_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1782_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1784_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1786_recIdents);
              _1783_i = (_1783_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_1782_generatedValues);
            RAST._IExpr _out410;
            DCOMP._IOwnership _out411;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out410, out _out411);
            r = _out410;
            resultingOwnership = _out411;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_ToMultiset) {
          DAST._IExpression _1787_expr = _source84.dtor_ToMultiset_a0;
          unmatched84 = false;
          {
            RAST._IExpr _1788_recursiveGen;
            DCOMP._IOwnership _1789___v143;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1790_recIdents;
            RAST._IExpr _out412;
            DCOMP._IOwnership _out413;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out414;
            (this).GenExpr(_1787_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out412, out _out413, out _out414);
            _1788_recursiveGen = _out412;
            _1789___v143 = _out413;
            _1790_recIdents = _out414;
            r = ((_1788_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _1790_recIdents;
            RAST._IExpr _out415;
            DCOMP._IOwnership _out416;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out415, out _out416);
            r = _out415;
            resultingOwnership = _out416;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1791_mapElems = _source84.dtor_mapElems;
          unmatched84 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1792_generatedValues;
            _1792_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1793_i;
            _1793_i = BigInteger.Zero;
            while ((_1793_i) < (new BigInteger((_1791_mapElems).Count))) {
              RAST._IExpr _1794_recursiveGenKey;
              DCOMP._IOwnership _1795___v144;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1796_recIdentsKey;
              RAST._IExpr _out417;
              DCOMP._IOwnership _out418;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out419;
              (this).GenExpr(((_1791_mapElems).Select(_1793_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out417, out _out418, out _out419);
              _1794_recursiveGenKey = _out417;
              _1795___v144 = _out418;
              _1796_recIdentsKey = _out419;
              RAST._IExpr _1797_recursiveGenValue;
              DCOMP._IOwnership _1798___v145;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1799_recIdentsValue;
              RAST._IExpr _out420;
              DCOMP._IOwnership _out421;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out422;
              (this).GenExpr(((_1791_mapElems).Select(_1793_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out420, out _out421, out _out422);
              _1797_recursiveGenValue = _out420;
              _1798___v145 = _out421;
              _1799_recIdentsValue = _out422;
              _1792_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1792_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1794_recursiveGenKey, _1797_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1796_recIdentsKey), _1799_recIdentsValue);
              _1793_i = (_1793_i) + (BigInteger.One);
            }
            _1793_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1800_arguments;
            _1800_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1793_i) < (new BigInteger((_1792_generatedValues).Count))) {
              RAST._IExpr _1801_genKey;
              _1801_genKey = ((_1792_generatedValues).Select(_1793_i)).dtor__0;
              RAST._IExpr _1802_genValue;
              _1802_genValue = ((_1792_generatedValues).Select(_1793_i)).dtor__1;
              _1800_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1800_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1801_genKey, _1802_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _1793_i = (_1793_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_1800_arguments);
            RAST._IExpr _out423;
            DCOMP._IOwnership _out424;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out423, out _out424);
            r = _out423;
            resultingOwnership = _out424;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_SeqUpdate) {
          DAST._IExpression _1803_expr = _source84.dtor_expr;
          DAST._IExpression _1804_index = _source84.dtor_indexExpr;
          DAST._IExpression _1805_value = _source84.dtor_value;
          unmatched84 = false;
          {
            RAST._IExpr _1806_exprR;
            DCOMP._IOwnership _1807___v146;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1808_exprIdents;
            RAST._IExpr _out425;
            DCOMP._IOwnership _out426;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out427;
            (this).GenExpr(_1803_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out425, out _out426, out _out427);
            _1806_exprR = _out425;
            _1807___v146 = _out426;
            _1808_exprIdents = _out427;
            RAST._IExpr _1809_indexR;
            DCOMP._IOwnership _1810_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1811_indexIdents;
            RAST._IExpr _out428;
            DCOMP._IOwnership _out429;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out430;
            (this).GenExpr(_1804_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out428, out _out429, out _out430);
            _1809_indexR = _out428;
            _1810_indexOwnership = _out429;
            _1811_indexIdents = _out430;
            RAST._IExpr _1812_valueR;
            DCOMP._IOwnership _1813_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1814_valueIdents;
            RAST._IExpr _out431;
            DCOMP._IOwnership _out432;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out433;
            (this).GenExpr(_1805_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out431, out _out432, out _out433);
            _1812_valueR = _out431;
            _1813_valueOwnership = _out432;
            _1814_valueIdents = _out433;
            r = ((_1806_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1809_indexR, _1812_valueR));
            RAST._IExpr _out434;
            DCOMP._IOwnership _out435;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out434, out _out435);
            r = _out434;
            resultingOwnership = _out435;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1808_exprIdents, _1811_indexIdents), _1814_valueIdents);
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_MapUpdate) {
          DAST._IExpression _1815_expr = _source84.dtor_expr;
          DAST._IExpression _1816_index = _source84.dtor_indexExpr;
          DAST._IExpression _1817_value = _source84.dtor_value;
          unmatched84 = false;
          {
            RAST._IExpr _1818_exprR;
            DCOMP._IOwnership _1819___v147;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1820_exprIdents;
            RAST._IExpr _out436;
            DCOMP._IOwnership _out437;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out438;
            (this).GenExpr(_1815_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out436, out _out437, out _out438);
            _1818_exprR = _out436;
            _1819___v147 = _out437;
            _1820_exprIdents = _out438;
            RAST._IExpr _1821_indexR;
            DCOMP._IOwnership _1822_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1823_indexIdents;
            RAST._IExpr _out439;
            DCOMP._IOwnership _out440;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out441;
            (this).GenExpr(_1816_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out439, out _out440, out _out441);
            _1821_indexR = _out439;
            _1822_indexOwnership = _out440;
            _1823_indexIdents = _out441;
            RAST._IExpr _1824_valueR;
            DCOMP._IOwnership _1825_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1826_valueIdents;
            RAST._IExpr _out442;
            DCOMP._IOwnership _out443;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out444;
            (this).GenExpr(_1817_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out442, out _out443, out _out444);
            _1824_valueR = _out442;
            _1825_valueOwnership = _out443;
            _1826_valueIdents = _out444;
            r = ((_1818_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1821_indexR, _1824_valueR));
            RAST._IExpr _out445;
            DCOMP._IOwnership _out446;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out445, out _out446);
            r = _out445;
            resultingOwnership = _out446;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1820_exprIdents, _1823_indexIdents), _1826_valueIdents);
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_This) {
          unmatched84 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source85 = selfIdent;
            bool unmatched85 = true;
            if (unmatched85) {
              if (_source85.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1827_id = _source85.dtor_value;
                unmatched85 = false;
                {
                  r = RAST.Expr.create_Identifier(_1827_id);
                  if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
                    r = (r).Clone();
                    resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
                  } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
                    r = RAST.__default.BoxNew((r).Clone());
                    resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
                  } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
                    if (!(_1827_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                      r = RAST.__default.Borrow(r);
                    }
                    resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
                  } else {
                    if (!(_1827_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                      r = RAST.__default.BorrowMut(r);
                    }
                    resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
                  }
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1827_id);
                }
              }
            }
            if (unmatched85) {
              unmatched85 = false;
              {
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")"));
                RAST._IExpr _out447;
                DCOMP._IOwnership _out448;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out447, out _out448);
                r = _out447;
                resultingOwnership = _out448;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              }
            }
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_Ite) {
          DAST._IExpression _1828_cond = _source84.dtor_cond;
          DAST._IExpression _1829_t = _source84.dtor_thn;
          DAST._IExpression _1830_f = _source84.dtor_els;
          unmatched84 = false;
          {
            RAST._IExpr _1831_cond;
            DCOMP._IOwnership _1832___v148;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1833_recIdentsCond;
            RAST._IExpr _out449;
            DCOMP._IOwnership _out450;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
            (this).GenExpr(_1828_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out449, out _out450, out _out451);
            _1831_cond = _out449;
            _1832___v148 = _out450;
            _1833_recIdentsCond = _out451;
            RAST._IExpr _1834_fExpr;
            DCOMP._IOwnership _1835_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1836_recIdentsF;
            RAST._IExpr _out452;
            DCOMP._IOwnership _out453;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out454;
            (this).GenExpr(_1830_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out452, out _out453, out _out454);
            _1834_fExpr = _out452;
            _1835_fOwned = _out453;
            _1836_recIdentsF = _out454;
            RAST._IExpr _1837_tExpr;
            DCOMP._IOwnership _1838___v149;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1839_recIdentsT;
            RAST._IExpr _out455;
            DCOMP._IOwnership _out456;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out457;
            (this).GenExpr(_1829_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out455, out _out456, out _out457);
            _1837_tExpr = _out455;
            _1838___v149 = _out456;
            _1839_recIdentsT = _out457;
            r = RAST.Expr.create_IfExpr(_1831_cond, _1837_tExpr, _1834_fExpr);
            RAST._IExpr _out458;
            DCOMP._IOwnership _out459;
            DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out458, out _out459);
            r = _out458;
            resultingOwnership = _out459;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1833_recIdentsCond, _1839_recIdentsT), _1836_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source84.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _1840_e = _source84.dtor_expr;
            DAST.Format._IUnaryOpFormat _1841_format = _source84.dtor_format1;
            unmatched84 = false;
            {
              RAST._IExpr _1842_recursiveGen;
              DCOMP._IOwnership _1843___v150;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1844_recIdents;
              RAST._IExpr _out460;
              DCOMP._IOwnership _out461;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out462;
              (this).GenExpr(_1840_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out460, out _out461, out _out462);
              _1842_recursiveGen = _out460;
              _1843___v150 = _out461;
              _1844_recIdents = _out462;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _1842_recursiveGen, _1841_format);
              RAST._IExpr _out463;
              DCOMP._IOwnership _out464;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out463, out _out464);
              r = _out463;
              resultingOwnership = _out464;
              readIdents = _1844_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source84.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _1845_e = _source84.dtor_expr;
            DAST.Format._IUnaryOpFormat _1846_format = _source84.dtor_format1;
            unmatched84 = false;
            {
              RAST._IExpr _1847_recursiveGen;
              DCOMP._IOwnership _1848___v151;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1849_recIdents;
              RAST._IExpr _out465;
              DCOMP._IOwnership _out466;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out467;
              (this).GenExpr(_1845_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out465, out _out466, out _out467);
              _1847_recursiveGen = _out465;
              _1848___v151 = _out466;
              _1849_recIdents = _out467;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _1847_recursiveGen, _1846_format);
              RAST._IExpr _out468;
              DCOMP._IOwnership _out469;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out468, out _out469);
              r = _out468;
              resultingOwnership = _out469;
              readIdents = _1849_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source84.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _1850_e = _source84.dtor_expr;
            DAST.Format._IUnaryOpFormat _1851_format = _source84.dtor_format1;
            unmatched84 = false;
            {
              RAST._IExpr _1852_recursiveGen;
              DCOMP._IOwnership _1853_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1854_recIdents;
              RAST._IExpr _out470;
              DCOMP._IOwnership _out471;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out472;
              (this).GenExpr(_1850_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out470, out _out471, out _out472);
              _1852_recursiveGen = _out470;
              _1853_recOwned = _out471;
              _1854_recIdents = _out472;
              r = ((_1852_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out473;
              DCOMP._IOwnership _out474;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out473, out _out474);
              r = _out473;
              resultingOwnership = _out474;
              readIdents = _1854_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_BinOp) {
          DAST._IBinOp _1855___v152 = _source84.dtor_op;
          DAST._IExpression _1856___v153 = _source84.dtor_left;
          DAST._IExpression _1857___v154 = _source84.dtor_right;
          DAST.Format._IBinaryOpFormat _1858___v155 = _source84.dtor_format2;
          unmatched84 = false;
          RAST._IExpr _out475;
          DCOMP._IOwnership _out476;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out477;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out475, out _out476, out _out477);
          r = _out475;
          resultingOwnership = _out476;
          readIdents = _out477;
        }
      }
      if (unmatched84) {
        if (_source84.is_ArrayLen) {
          DAST._IExpression _1859_expr = _source84.dtor_expr;
          DAST._IType _1860_exprType = _source84.dtor_exprType;
          BigInteger _1861_dim = _source84.dtor_dim;
          bool _1862_native = _source84.dtor_native;
          unmatched84 = false;
          {
            RAST._IExpr _1863_recursiveGen;
            DCOMP._IOwnership _1864___v156;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1865_recIdents;
            RAST._IExpr _out478;
            DCOMP._IOwnership _out479;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out480;
            (this).GenExpr(_1859_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out478, out _out479, out _out480);
            _1863_recursiveGen = _out478;
            _1864___v156 = _out479;
            _1865_recIdents = _out480;
            RAST._IType _1866_arrayType;
            RAST._IType _out481;
            _out481 = (this).GenType(_1860_exprType, false, false);
            _1866_arrayType = _out481;
            if (!((_1866_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _1867_msg;
              _1867_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_1866_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1867_msg);
              r = RAST.Expr.create_RawExpr(_1867_msg);
            } else {
              RAST._IType _1868_underlying;
              _1868_underlying = (_1866_arrayType).ObjectOrPointerUnderlying();
              if (((_1861_dim).Sign == 0) && ((_1868_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_1863_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_1861_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_1863_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = (((this).read__macro).Apply1(_1863_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Length"), Std.Strings.__default.OfNat(_1861_dim)));
                }
              }
              if (!(_1862_native)) {
                r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(r);
              }
            }
            RAST._IExpr _out482;
            DCOMP._IOwnership _out483;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out482, out _out483);
            r = _out482;
            resultingOwnership = _out483;
            readIdents = _1865_recIdents;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_MapKeys) {
          DAST._IExpression _1869_expr = _source84.dtor_expr;
          unmatched84 = false;
          {
            RAST._IExpr _1870_recursiveGen;
            DCOMP._IOwnership _1871___v157;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1872_recIdents;
            RAST._IExpr _out484;
            DCOMP._IOwnership _out485;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out486;
            (this).GenExpr(_1869_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out484, out _out485, out _out486);
            _1870_recursiveGen = _out484;
            _1871___v157 = _out485;
            _1872_recIdents = _out486;
            readIdents = _1872_recIdents;
            r = ((_1870_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out487;
            DCOMP._IOwnership _out488;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out487, out _out488);
            r = _out487;
            resultingOwnership = _out488;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_MapValues) {
          DAST._IExpression _1873_expr = _source84.dtor_expr;
          unmatched84 = false;
          {
            RAST._IExpr _1874_recursiveGen;
            DCOMP._IOwnership _1875___v158;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1876_recIdents;
            RAST._IExpr _out489;
            DCOMP._IOwnership _out490;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out491;
            (this).GenExpr(_1873_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out489, out _out490, out _out491);
            _1874_recursiveGen = _out489;
            _1875___v158 = _out490;
            _1876_recIdents = _out491;
            readIdents = _1876_recIdents;
            r = ((_1874_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out492;
            DCOMP._IOwnership _out493;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out492, out _out493);
            r = _out492;
            resultingOwnership = _out493;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_SelectFn) {
          DAST._IExpression _1877_on = _source84.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1878_field = _source84.dtor_field;
          bool _1879_isDatatype = _source84.dtor_onDatatype;
          bool _1880_isStatic = _source84.dtor_isStatic;
          BigInteger _1881_arity = _source84.dtor_arity;
          unmatched84 = false;
          {
            RAST._IExpr _1882_onExpr;
            DCOMP._IOwnership _1883_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1884_recIdents;
            RAST._IExpr _out494;
            DCOMP._IOwnership _out495;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out496;
            (this).GenExpr(_1877_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out494, out _out495, out _out496);
            _1882_onExpr = _out494;
            _1883_onOwned = _out495;
            _1884_recIdents = _out496;
            Dafny.ISequence<Dafny.Rune> _1885_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _1886_onString;
            _1886_onString = (_1882_onExpr)._ToString(DCOMP.__default.IND);
            if (_1880_isStatic) {
              _1885_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1886_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_1878_field));
            } else {
              _1885_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _1885_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1885_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _1886_onString), ((object.Equals(_1883_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _1887_args;
              _1887_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _1888_i;
              _1888_i = BigInteger.Zero;
              while ((_1888_i) < (_1881_arity)) {
                if ((_1888_i).Sign == 1) {
                  _1887_args = Dafny.Sequence<Dafny.Rune>.Concat(_1887_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _1887_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1887_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_1888_i));
                _1888_i = (_1888_i) + (BigInteger.One);
              }
              _1885_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1885_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _1887_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _1885_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1885_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_1878_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1887_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _1885_s = Dafny.Sequence<Dafny.Rune>.Concat(_1885_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _1885_s = Dafny.Sequence<Dafny.Rune>.Concat(_1885_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _1889_typeShape;
            _1889_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _1890_i;
            _1890_i = BigInteger.Zero;
            while ((_1890_i) < (_1881_arity)) {
              if ((_1890_i).Sign == 1) {
                _1889_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1889_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _1889_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1889_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _1890_i = (_1890_i) + (BigInteger.One);
            }
            _1889_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1889_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _1885_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _1885_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _1889_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_1885_s);
            RAST._IExpr _out497;
            DCOMP._IOwnership _out498;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out497, out _out498);
            r = _out497;
            resultingOwnership = _out498;
            readIdents = _1884_recIdents;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_Select) {
          DAST._IExpression expr0 = _source84.dtor_expr;
          if (expr0.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1891_c = expr0.dtor_Companion_a0;
            Dafny.ISequence<Dafny.Rune> _1892_field = _source84.dtor_field;
            bool _1893_isConstant = _source84.dtor_isConstant;
            bool _1894_isDatatype = _source84.dtor_onDatatype;
            DAST._IType _1895_fieldType = _source84.dtor_fieldType;
            unmatched84 = false;
            {
              RAST._IExpr _1896_onExpr;
              DCOMP._IOwnership _1897_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1898_recIdents;
              RAST._IExpr _out499;
              DCOMP._IOwnership _out500;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out501;
              (this).GenExpr(DAST.Expression.create_Companion(_1891_c), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out499, out _out500, out _out501);
              _1896_onExpr = _out499;
              _1897_onOwned = _out500;
              _1898_recIdents = _out501;
              r = ((_1896_onExpr).MSel(DCOMP.__default.escapeName(_1892_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out502;
              DCOMP._IOwnership _out503;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out502, out _out503);
              r = _out502;
              resultingOwnership = _out503;
              readIdents = _1898_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_Select) {
          DAST._IExpression _1899_on = _source84.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1900_field = _source84.dtor_field;
          bool _1901_isConstant = _source84.dtor_isConstant;
          bool _1902_isDatatype = _source84.dtor_onDatatype;
          DAST._IType _1903_fieldType = _source84.dtor_fieldType;
          unmatched84 = false;
          {
            if (_1902_isDatatype) {
              RAST._IExpr _1904_onExpr;
              DCOMP._IOwnership _1905_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1906_recIdents;
              RAST._IExpr _out504;
              DCOMP._IOwnership _out505;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out506;
              (this).GenExpr(_1899_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out504, out _out505, out _out506);
              _1904_onExpr = _out504;
              _1905_onOwned = _out505;
              _1906_recIdents = _out506;
              r = ((_1904_onExpr).Sel(DCOMP.__default.escapeName(_1900_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _1907_typ;
              RAST._IType _out507;
              _out507 = (this).GenType(_1903_fieldType, false, false);
              _1907_typ = _out507;
              RAST._IExpr _out508;
              DCOMP._IOwnership _out509;
              DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out508, out _out509);
              r = _out508;
              resultingOwnership = _out509;
              readIdents = _1906_recIdents;
            } else {
              RAST._IExpr _1908_onExpr;
              DCOMP._IOwnership _1909_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1910_recIdents;
              RAST._IExpr _out510;
              DCOMP._IOwnership _out511;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out512;
              (this).GenExpr(_1899_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out510, out _out511, out _out512);
              _1908_onExpr = _out510;
              _1909_onOwned = _out511;
              _1910_recIdents = _out512;
              r = _1908_onExpr;
              if (!object.Equals(_1908_onExpr, RAST.__default.self)) {
                RAST._IExpr _source86 = _1908_onExpr;
                bool unmatched86 = true;
                if (unmatched86) {
                  if (_source86.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> op15 = _source86.dtor_op1;
                    if (object.Equals(op15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                      RAST._IExpr underlying5 = _source86.dtor_underlying;
                      if (underlying5.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name21 = underlying5.dtor_name;
                        if (object.Equals(name21, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                          DAST.Format._IUnaryOpFormat _1911___v159 = _source86.dtor_format;
                          unmatched86 = false;
                          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
                        }
                      }
                    }
                  }
                }
                if (unmatched86) {
                  RAST._IExpr _1912___v160 = _source86;
                  unmatched86 = false;
                }
                if (((this).ObjectType).is_RcMut) {
                  r = (r).Clone();
                }
                r = ((this).read__macro).Apply1(r);
              }
              r = (r).Sel(DCOMP.__default.escapeName(_1900_field));
              if (_1901_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              DCOMP._IOwnership _1913_fromOwnership;
              _1913_fromOwnership = ((_1901_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out513;
              DCOMP._IOwnership _out514;
              DCOMP.COMP.FromOwnership(r, _1913_fromOwnership, expectedOwnership, out _out513, out _out514);
              r = _out513;
              resultingOwnership = _out514;
              readIdents = _1910_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_Index) {
          DAST._IExpression _1914_on = _source84.dtor_expr;
          DAST._ICollKind _1915_collKind = _source84.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _1916_indices = _source84.dtor_indices;
          unmatched84 = false;
          {
            RAST._IExpr _1917_onExpr;
            DCOMP._IOwnership _1918_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1919_recIdents;
            RAST._IExpr _out515;
            DCOMP._IOwnership _out516;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out517;
            (this).GenExpr(_1914_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out515, out _out516, out _out517);
            _1917_onExpr = _out515;
            _1918_onOwned = _out516;
            _1919_recIdents = _out517;
            readIdents = _1919_recIdents;
            r = _1917_onExpr;
            BigInteger _1920_i;
            _1920_i = BigInteger.Zero;
            while ((_1920_i) < (new BigInteger((_1916_indices).Count))) {
              if (object.Equals(_1915_collKind, DAST.CollKind.create_Array())) {
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              RAST._IExpr _1921_idx;
              DCOMP._IOwnership _1922_idxOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1923_recIdentsIdx;
              RAST._IExpr _out518;
              DCOMP._IOwnership _out519;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out520;
              (this).GenExpr((_1916_indices).Select(_1920_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out518, out _out519, out _out520);
              _1921_idx = _out518;
              _1922_idxOwned = _out519;
              _1923_recIdentsIdx = _out520;
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_1921_idx);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1923_recIdentsIdx);
              _1920_i = (_1920_i) + (BigInteger.One);
            }
            RAST._IExpr _out521;
            DCOMP._IOwnership _out522;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out521, out _out522);
            r = _out521;
            resultingOwnership = _out522;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_IndexRange) {
          DAST._IExpression _1924_on = _source84.dtor_expr;
          bool _1925_isArray = _source84.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _1926_low = _source84.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _1927_high = _source84.dtor_high;
          unmatched84 = false;
          {
            RAST._IExpr _1928_onExpr;
            DCOMP._IOwnership _1929_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1930_recIdents;
            RAST._IExpr _out523;
            DCOMP._IOwnership _out524;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
            (this).GenExpr(_1924_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out523, out _out524, out _out525);
            _1928_onExpr = _out523;
            _1929_onOwned = _out524;
            _1930_recIdents = _out525;
            readIdents = _1930_recIdents;
            Dafny.ISequence<Dafny.Rune> _1931_methodName;
            _1931_methodName = (((_1926_low).is_Some) ? ((((_1927_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_1927_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _1932_arguments;
            _1932_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source87 = _1926_low;
            bool unmatched87 = true;
            if (unmatched87) {
              if (_source87.is_Some) {
                DAST._IExpression _1933_l = _source87.dtor_value;
                unmatched87 = false;
                {
                  RAST._IExpr _1934_lExpr;
                  DCOMP._IOwnership _1935___v161;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1936_recIdentsL;
                  RAST._IExpr _out526;
                  DCOMP._IOwnership _out527;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out528;
                  (this).GenExpr(_1933_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out526, out _out527, out _out528);
                  _1934_lExpr = _out526;
                  _1935___v161 = _out527;
                  _1936_recIdentsL = _out528;
                  _1932_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1932_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1934_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1936_recIdentsL);
                }
              }
            }
            if (unmatched87) {
              unmatched87 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source88 = _1927_high;
            bool unmatched88 = true;
            if (unmatched88) {
              if (_source88.is_Some) {
                DAST._IExpression _1937_h = _source88.dtor_value;
                unmatched88 = false;
                {
                  RAST._IExpr _1938_hExpr;
                  DCOMP._IOwnership _1939___v162;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1940_recIdentsH;
                  RAST._IExpr _out529;
                  DCOMP._IOwnership _out530;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out531;
                  (this).GenExpr(_1937_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out529, out _out530, out _out531);
                  _1938_hExpr = _out529;
                  _1939___v162 = _out530;
                  _1940_recIdentsH = _out531;
                  _1932_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1932_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1938_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1940_recIdentsH);
                }
              }
            }
            if (unmatched88) {
              unmatched88 = false;
            }
            r = _1928_onExpr;
            if (_1925_isArray) {
              if (!(_1931_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _1931_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1931_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _1931_methodName))).Apply(_1932_arguments);
            } else {
              if (!(_1931_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_1931_methodName)).Apply(_1932_arguments);
              }
            }
            RAST._IExpr _out532;
            DCOMP._IOwnership _out533;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out532, out _out533);
            r = _out532;
            resultingOwnership = _out533;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_TupleSelect) {
          DAST._IExpression _1941_on = _source84.dtor_expr;
          BigInteger _1942_idx = _source84.dtor_index;
          DAST._IType _1943_fieldType = _source84.dtor_fieldType;
          unmatched84 = false;
          {
            RAST._IExpr _1944_onExpr;
            DCOMP._IOwnership _1945_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1946_recIdents;
            RAST._IExpr _out534;
            DCOMP._IOwnership _out535;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out536;
            (this).GenExpr(_1941_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out534, out _out535, out _out536);
            _1944_onExpr = _out534;
            _1945_onOwnership = _out535;
            _1946_recIdents = _out536;
            Dafny.ISequence<Dafny.Rune> _1947_selName;
            _1947_selName = Std.Strings.__default.OfNat(_1942_idx);
            DAST._IType _source89 = _1943_fieldType;
            bool unmatched89 = true;
            if (unmatched89) {
              if (_source89.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1948_tps = _source89.dtor_Tuple_a0;
                unmatched89 = false;
                if (((_1943_fieldType).is_Tuple) && ((new BigInteger((_1948_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _1947_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1947_selName);
                }
              }
            }
            if (unmatched89) {
              DAST._IType _1949___v163 = _source89;
              unmatched89 = false;
            }
            r = (_1944_onExpr).Sel(_1947_selName);
            RAST._IExpr _out537;
            DCOMP._IOwnership _out538;
            DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out537, out _out538);
            r = _out537;
            resultingOwnership = _out538;
            readIdents = _1946_recIdents;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_Call) {
          DAST._IExpression _1950_on = _source84.dtor_on;
          DAST._ICallName _1951_name = _source84.dtor_callName;
          Dafny.ISequence<DAST._IType> _1952_typeArgs = _source84.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1953_args = _source84.dtor_args;
          unmatched84 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IExpr _1954_onExpr;
            DCOMP._IOwnership _1955___v164;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1956_recIdents;
            RAST._IExpr _out539;
            DCOMP._IOwnership _out540;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
            (this).GenExpr(_1950_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out539, out _out540, out _out541);
            _1954_onExpr = _out539;
            _1955___v164 = _out540;
            _1956_recIdents = _out541;
            Dafny.ISequence<RAST._IType> _1957_typeExprs;
            _1957_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
            if ((new BigInteger((_1952_typeArgs).Count)) >= (BigInteger.One)) {
              BigInteger _hi39 = new BigInteger((_1952_typeArgs).Count);
              for (BigInteger _1958_typeI = BigInteger.Zero; _1958_typeI < _hi39; _1958_typeI++) {
                RAST._IType _1959_typeExpr;
                RAST._IType _out542;
                _out542 = (this).GenType((_1952_typeArgs).Select(_1958_typeI), false, false);
                _1959_typeExpr = _out542;
                _1957_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1957_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1959_typeExpr));
              }
            }
            Dafny.ISequence<RAST._IExpr> _1960_argExprs;
            _1960_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi40 = new BigInteger((_1953_args).Count);
            for (BigInteger _1961_i = BigInteger.Zero; _1961_i < _hi40; _1961_i++) {
              DCOMP._IOwnership _1962_argOwnership;
              _1962_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              if (((_1951_name).is_CallName) && ((_1961_i) < (new BigInteger((((_1951_name).dtor_signature)).Count)))) {
                RAST._IType _1963_tpe;
                RAST._IType _out543;
                _out543 = (this).GenType(((((_1951_name).dtor_signature)).Select(_1961_i)).dtor_typ, false, false);
                _1963_tpe = _out543;
                if ((_1963_tpe).CanReadWithoutClone()) {
                  _1962_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
                }
              }
              RAST._IExpr _1964_argExpr;
              DCOMP._IOwnership _1965___v165;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1966_argIdents;
              RAST._IExpr _out544;
              DCOMP._IOwnership _out545;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out546;
              (this).GenExpr((_1953_args).Select(_1961_i), selfIdent, env, _1962_argOwnership, out _out544, out _out545, out _out546);
              _1964_argExpr = _out544;
              _1965___v165 = _out545;
              _1966_argIdents = _out546;
              _1960_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1960_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1964_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1966_argIdents);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1956_recIdents);
            Dafny.ISequence<Dafny.Rune> _1967_renderedName;
            _1967_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
              DAST._ICallName _source90 = _1951_name;
              bool unmatched90 = true;
              if (unmatched90) {
                if (_source90.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _1968_ident = _source90.dtor_name;
                  Std.Wrappers._IOption<DAST._IType> _1969___v166 = _source90.dtor_onType;
                  Std.Wrappers._IOption<DAST._IFormal> _1970___v167 = _source90.dtor_receiverArgs;
                  Dafny.ISequence<DAST._IFormal> _1971___v168 = _source90.dtor_signature;
                  unmatched90 = false;
                  return DCOMP.__default.escapeName(_1968_ident);
                }
              }
              if (unmatched90) {
                bool disjunctiveMatch13 = false;
                if (_source90.is_MapBuilderAdd) {
                  disjunctiveMatch13 = true;
                }
                if (_source90.is_SetBuilderAdd) {
                  disjunctiveMatch13 = true;
                }
                if (disjunctiveMatch13) {
                  unmatched90 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                }
              }
              if (unmatched90) {
                bool disjunctiveMatch14 = false;
                disjunctiveMatch14 = true;
                disjunctiveMatch14 = true;
                if (disjunctiveMatch14) {
                  unmatched90 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                }
              }
              throw new System.Exception("unexpected control point");
            }))();
            DAST._IExpression _source91 = _1950_on;
            bool unmatched91 = true;
            if (unmatched91) {
              if (_source91.is_Companion) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1972___v169 = _source91.dtor_Companion_a0;
                unmatched91 = false;
                {
                  _1954_onExpr = (_1954_onExpr).MSel(_1967_renderedName);
                }
              }
            }
            if (unmatched91) {
              DAST._IExpression _1973___v170 = _source91;
              unmatched91 = false;
              {
                if (!object.Equals(_1954_onExpr, RAST.__default.self)) {
                  DAST._ICallName _source92 = _1951_name;
                  bool unmatched92 = true;
                  if (unmatched92) {
                    if (_source92.is_CallName) {
                      Dafny.ISequence<Dafny.Rune> _1974___v171 = _source92.dtor_name;
                      Std.Wrappers._IOption<DAST._IType> onType1 = _source92.dtor_onType;
                      if (onType1.is_Some) {
                        DAST._IType _1975_tpe = onType1.dtor_value;
                        Std.Wrappers._IOption<DAST._IFormal> _1976___v172 = _source92.dtor_receiverArgs;
                        Dafny.ISequence<DAST._IFormal> _1977___v173 = _source92.dtor_signature;
                        unmatched92 = false;
                        RAST._IType _1978_typ;
                        RAST._IType _out547;
                        _out547 = (this).GenType(_1975_tpe, false, false);
                        _1978_typ = _out547;
                        if ((_1978_typ).IsObjectOrPointer()) {
                          _1954_onExpr = ((this).read__macro).Apply1(_1954_onExpr);
                        }
                      }
                    }
                  }
                  if (unmatched92) {
                    DAST._ICallName _1979___v174 = _source92;
                    unmatched92 = false;
                  }
                }
                _1954_onExpr = (_1954_onExpr).Sel(_1967_renderedName);
              }
            }
            r = _1954_onExpr;
            if ((new BigInteger((_1957_typeExprs).Count)).Sign == 1) {
              r = (r).ApplyType(_1957_typeExprs);
            }
            r = (r).Apply(_1960_argExprs);
            RAST._IExpr _out548;
            DCOMP._IOwnership _out549;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out548, out _out549);
            r = _out548;
            resultingOwnership = _out549;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _1980_paramsDafny = _source84.dtor_params;
          DAST._IType _1981_retType = _source84.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _1982_body = _source84.dtor_body;
          unmatched84 = false;
          {
            Dafny.ISequence<RAST._IFormal> _1983_params;
            Dafny.ISequence<RAST._IFormal> _out550;
            _out550 = (this).GenParams(_1980_paramsDafny);
            _1983_params = _out550;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1984_paramNames;
            _1984_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1985_paramTypesMap;
            _1985_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi41 = new BigInteger((_1983_params).Count);
            for (BigInteger _1986_i = BigInteger.Zero; _1986_i < _hi41; _1986_i++) {
              Dafny.ISequence<Dafny.Rune> _1987_name;
              _1987_name = ((_1983_params).Select(_1986_i)).dtor_name;
              _1984_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1984_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1987_name));
              _1985_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1985_paramTypesMap, _1987_name, ((_1983_params).Select(_1986_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _1988_subEnv;
            _1988_subEnv = (env).merge(DCOMP.Environment.create(_1984_paramNames, _1985_paramTypesMap));
            RAST._IExpr _1989_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1990_recIdents;
            DCOMP._IEnvironment _1991___v175;
            RAST._IExpr _out551;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out552;
            DCOMP._IEnvironment _out553;
            (this).GenStmts(_1982_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), _1988_subEnv, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out551, out _out552, out _out553);
            _1989_recursiveGen = _out551;
            _1990_recIdents = _out552;
            _1991___v175 = _out553;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _1990_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1990_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_1992_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll6 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in (_1992_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _1993_name = (Dafny.ISequence<Dafny.Rune>)_compr_6;
                if ((_1992_paramNames).Contains(_1993_name)) {
                  _coll6.Add(_1993_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll6);
            }))())(_1984_paramNames));
            RAST._IExpr _1994_allReadCloned;
            _1994_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_1990_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _1995_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_1990_recIdents).Elements) {
                _1995_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_1990_recIdents).Contains(_1995_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 4287)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) && ((_1995_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
                  _1994_allReadCloned = (_1994_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some((RAST.__default.self).Clone())));
                }
              } else if (!((_1984_paramNames).Contains(_1995_next))) {
                RAST._IExpr _1996_copy;
                _1996_copy = (RAST.Expr.create_Identifier(_1995_next)).Clone();
                _1994_allReadCloned = (_1994_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1995_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1996_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1995_next));
              }
              _1990_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1990_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1995_next));
            }
            RAST._IType _1997_retTypeGen;
            RAST._IType _out554;
            _out554 = (this).GenType(_1981_retType, false, true);
            _1997_retTypeGen = _out554;
            r = RAST.Expr.create_Block((_1994_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_1983_params, Std.Wrappers.Option<RAST._IType>.create_Some(_1997_retTypeGen), RAST.Expr.create_Block(_1989_recursiveGen)))));
            RAST._IExpr _out555;
            DCOMP._IOwnership _out556;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out555, out _out556);
            r = _out555;
            resultingOwnership = _out556;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _1998_values = _source84.dtor_values;
          DAST._IType _1999_retType = _source84.dtor_retType;
          DAST._IExpression _2000_expr = _source84.dtor_expr;
          unmatched84 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2001_paramNames;
            _2001_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2002_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out557;
            _out557 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2003_value) => {
              return (_2003_value).dtor__0;
            })), _1998_values));
            _2002_paramFormals = _out557;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2004_paramTypes;
            _2004_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2005_paramNamesSet;
            _2005_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi42 = new BigInteger((_1998_values).Count);
            for (BigInteger _2006_i = BigInteger.Zero; _2006_i < _hi42; _2006_i++) {
              Dafny.ISequence<Dafny.Rune> _2007_name;
              _2007_name = (((_1998_values).Select(_2006_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2008_rName;
              _2008_rName = DCOMP.__default.escapeName(_2007_name);
              _2001_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2001_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2008_rName));
              _2004_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2004_paramTypes, _2008_rName, ((_2002_paramFormals).Select(_2006_i)).dtor_tpe);
              _2005_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2005_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2008_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi43 = new BigInteger((_1998_values).Count);
            for (BigInteger _2009_i = BigInteger.Zero; _2009_i < _hi43; _2009_i++) {
              RAST._IType _2010_typeGen;
              RAST._IType _out558;
              _out558 = (this).GenType((((_1998_values).Select(_2009_i)).dtor__0).dtor_typ, false, true);
              _2010_typeGen = _out558;
              RAST._IExpr _2011_valueGen;
              DCOMP._IOwnership _2012___v176;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2013_recIdents;
              RAST._IExpr _out559;
              DCOMP._IOwnership _out560;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out561;
              (this).GenExpr(((_1998_values).Select(_2009_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out559, out _out560, out _out561);
              _2011_valueGen = _out559;
              _2012___v176 = _out560;
              _2013_recIdents = _out561;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_1998_values).Select(_2009_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2010_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2011_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2013_recIdents);
            }
            DCOMP._IEnvironment _2014_newEnv;
            _2014_newEnv = DCOMP.Environment.create(_2001_paramNames, _2004_paramTypes);
            RAST._IExpr _2015_recGen;
            DCOMP._IOwnership _2016_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2017_recIdents;
            RAST._IExpr _out562;
            DCOMP._IOwnership _out563;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out564;
            (this).GenExpr(_2000_expr, selfIdent, _2014_newEnv, expectedOwnership, out _out562, out _out563, out _out564);
            _2015_recGen = _out562;
            _2016_recOwned = _out563;
            _2017_recIdents = _out564;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2017_recIdents, _2005_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2015_recGen));
            RAST._IExpr _out565;
            DCOMP._IOwnership _out566;
            DCOMP.COMP.FromOwnership(r, _2016_recOwned, expectedOwnership, out _out565, out _out566);
            r = _out565;
            resultingOwnership = _out566;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2018_name = _source84.dtor_name;
          DAST._IType _2019_tpe = _source84.dtor_typ;
          DAST._IExpression _2020_value = _source84.dtor_value;
          DAST._IExpression _2021_iifeBody = _source84.dtor_iifeBody;
          unmatched84 = false;
          {
            RAST._IExpr _2022_valueGen;
            DCOMP._IOwnership _2023___v177;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2024_recIdents;
            RAST._IExpr _out567;
            DCOMP._IOwnership _out568;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out569;
            (this).GenExpr(_2020_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out567, out _out568, out _out569);
            _2022_valueGen = _out567;
            _2023___v177 = _out568;
            _2024_recIdents = _out569;
            readIdents = _2024_recIdents;
            RAST._IType _2025_valueTypeGen;
            RAST._IType _out570;
            _out570 = (this).GenType(_2019_tpe, false, true);
            _2025_valueTypeGen = _out570;
            RAST._IExpr _2026_bodyGen;
            DCOMP._IOwnership _2027___v178;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2028_bodyIdents;
            RAST._IExpr _out571;
            DCOMP._IOwnership _out572;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out573;
            (this).GenExpr(_2021_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out571, out _out572, out _out573);
            _2026_bodyGen = _out571;
            _2027___v178 = _out572;
            _2028_bodyIdents = _out573;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2028_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_2018_name)))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_2018_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_2025_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2022_valueGen))).Then(_2026_bodyGen));
            RAST._IExpr _out574;
            DCOMP._IOwnership _out575;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out574, out _out575);
            r = _out574;
            resultingOwnership = _out575;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_Apply) {
          DAST._IExpression _2029_func = _source84.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2030_args = _source84.dtor_args;
          unmatched84 = false;
          {
            RAST._IExpr _2031_funcExpr;
            DCOMP._IOwnership _2032___v179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2033_recIdents;
            RAST._IExpr _out576;
            DCOMP._IOwnership _out577;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out578;
            (this).GenExpr(_2029_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out576, out _out577, out _out578);
            _2031_funcExpr = _out576;
            _2032___v179 = _out577;
            _2033_recIdents = _out578;
            readIdents = _2033_recIdents;
            Dafny.ISequence<RAST._IExpr> _2034_rArgs;
            _2034_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi44 = new BigInteger((_2030_args).Count);
            for (BigInteger _2035_i = BigInteger.Zero; _2035_i < _hi44; _2035_i++) {
              RAST._IExpr _2036_argExpr;
              DCOMP._IOwnership _2037_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2038_argIdents;
              RAST._IExpr _out579;
              DCOMP._IOwnership _out580;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out581;
              (this).GenExpr((_2030_args).Select(_2035_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out579, out _out580, out _out581);
              _2036_argExpr = _out579;
              _2037_argOwned = _out580;
              _2038_argIdents = _out581;
              _2034_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2034_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2036_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2038_argIdents);
            }
            r = (_2031_funcExpr).Apply(_2034_rArgs);
            RAST._IExpr _out582;
            DCOMP._IOwnership _out583;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out582, out _out583);
            r = _out582;
            resultingOwnership = _out583;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_TypeTest) {
          DAST._IExpression _2039_on = _source84.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2040_dType = _source84.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2041_variant = _source84.dtor_variant;
          unmatched84 = false;
          {
            RAST._IExpr _2042_exprGen;
            DCOMP._IOwnership _2043___v180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2044_recIdents;
            RAST._IExpr _out584;
            DCOMP._IOwnership _out585;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out586;
            (this).GenExpr(_2039_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out584, out _out585, out _out586);
            _2042_exprGen = _out584;
            _2043___v180 = _out585;
            _2044_recIdents = _out586;
            RAST._IType _2045_dTypePath;
            RAST._IType _out587;
            _out587 = DCOMP.COMP.GenPath(_2040_dType);
            _2045_dTypePath = _out587;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2042_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_2045_dTypePath).MSel(DCOMP.__default.escapeName(_2041_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out588;
            DCOMP._IOwnership _out589;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out588, out _out589);
            r = _out588;
            resultingOwnership = _out589;
            readIdents = _2044_recIdents;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_BoolBoundedPool) {
          unmatched84 = false;
          {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
            RAST._IExpr _out590;
            DCOMP._IOwnership _out591;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out590, out _out591);
            r = _out590;
            resultingOwnership = _out591;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_SetBoundedPool) {
          DAST._IExpression _2046_of = _source84.dtor_of;
          unmatched84 = false;
          {
            RAST._IExpr _2047_exprGen;
            DCOMP._IOwnership _2048___v181;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2049_recIdents;
            RAST._IExpr _out592;
            DCOMP._IOwnership _out593;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out594;
            (this).GenExpr(_2046_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out592, out _out593, out _out594);
            _2047_exprGen = _out592;
            _2048___v181 = _out593;
            _2049_recIdents = _out594;
            r = ((_2047_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out595;
            DCOMP._IOwnership _out596;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out595, out _out596);
            r = _out595;
            resultingOwnership = _out596;
            readIdents = _2049_recIdents;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_SeqBoundedPool) {
          DAST._IExpression _2050_of = _source84.dtor_of;
          bool _2051_includeDuplicates = _source84.dtor_includeDuplicates;
          unmatched84 = false;
          {
            RAST._IExpr _2052_exprGen;
            DCOMP._IOwnership _2053___v182;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2054_recIdents;
            RAST._IExpr _out597;
            DCOMP._IOwnership _out598;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out599;
            (this).GenExpr(_2050_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out597, out _out598, out _out599);
            _2052_exprGen = _out597;
            _2053___v182 = _out598;
            _2054_recIdents = _out599;
            r = ((_2052_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2051_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out600;
            DCOMP._IOwnership _out601;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out600, out _out601);
            r = _out600;
            resultingOwnership = _out601;
            readIdents = _2054_recIdents;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_MapBoundedPool) {
          DAST._IExpression _2055_of = _source84.dtor_of;
          unmatched84 = false;
          {
            RAST._IExpr _2056_exprGen;
            DCOMP._IOwnership _2057___v183;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2058_recIdents;
            RAST._IExpr _out602;
            DCOMP._IOwnership _out603;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out604;
            (this).GenExpr(_2055_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out602, out _out603, out _out604);
            _2056_exprGen = _out602;
            _2057___v183 = _out603;
            _2058_recIdents = _out604;
            r = ((((_2056_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2058_recIdents;
            RAST._IExpr _out605;
            DCOMP._IOwnership _out606;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out605, out _out606);
            r = _out605;
            resultingOwnership = _out606;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_IntRange) {
          DAST._IExpression _2059_lo = _source84.dtor_lo;
          DAST._IExpression _2060_hi = _source84.dtor_hi;
          bool _2061_up = _source84.dtor_up;
          unmatched84 = false;
          {
            RAST._IExpr _2062_lo;
            DCOMP._IOwnership _2063___v184;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2064_recIdentsLo;
            RAST._IExpr _out607;
            DCOMP._IOwnership _out608;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out609;
            (this).GenExpr(_2059_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out607, out _out608, out _out609);
            _2062_lo = _out607;
            _2063___v184 = _out608;
            _2064_recIdentsLo = _out609;
            RAST._IExpr _2065_hi;
            DCOMP._IOwnership _2066___v185;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2067_recIdentsHi;
            RAST._IExpr _out610;
            DCOMP._IOwnership _out611;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out612;
            (this).GenExpr(_2060_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out610, out _out611, out _out612);
            _2065_hi = _out610;
            _2066___v185 = _out611;
            _2067_recIdentsHi = _out612;
            if (_2061_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2062_lo, _2065_hi));
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2065_hi, _2062_lo));
            }
            RAST._IExpr _out613;
            DCOMP._IOwnership _out614;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out613, out _out614);
            r = _out613;
            resultingOwnership = _out614;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2064_recIdentsLo, _2067_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_UnboundedIntRange) {
          DAST._IExpression _2068_start = _source84.dtor_start;
          bool _2069_up = _source84.dtor_up;
          unmatched84 = false;
          {
            RAST._IExpr _2070_start;
            DCOMP._IOwnership _2071___v186;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2072_recIdentStart;
            RAST._IExpr _out615;
            DCOMP._IOwnership _out616;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out617;
            (this).GenExpr(_2068_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out615, out _out616, out _out617);
            _2070_start = _out615;
            _2071___v186 = _out616;
            _2072_recIdentStart = _out617;
            if (_2069_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).Apply1(_2070_start);
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).Apply1(_2070_start);
            }
            RAST._IExpr _out618;
            DCOMP._IOwnership _out619;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out618, out _out619);
            r = _out618;
            resultingOwnership = _out619;
            readIdents = _2072_recIdentStart;
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_MapBuilder) {
          DAST._IType _2073_keyType = _source84.dtor_keyType;
          DAST._IType _2074_valueType = _source84.dtor_valueType;
          unmatched84 = false;
          {
            RAST._IType _2075_kType;
            RAST._IType _out620;
            _out620 = (this).GenType(_2073_keyType, false, false);
            _2075_kType = _out620;
            RAST._IType _2076_vType;
            RAST._IType _out621;
            _out621 = (this).GenType(_2074_valueType, false, false);
            _2076_vType = _out621;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2075_kType, _2076_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out622;
            DCOMP._IOwnership _out623;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out622, out _out623);
            r = _out622;
            resultingOwnership = _out623;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_SetBuilder) {
          DAST._IType _2077_elemType = _source84.dtor_elemType;
          unmatched84 = false;
          {
            RAST._IType _2078_eType;
            RAST._IType _out624;
            _out624 = (this).GenType(_2077_elemType, false, false);
            _2078_eType = _out624;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2078_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out625;
            DCOMP._IOwnership _out626;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out625, out _out626);
            r = _out625;
            resultingOwnership = _out626;
            return ;
          }
        }
      }
      if (unmatched84) {
        DAST._IType _2079_elemType = _source84.dtor_elemType;
        DAST._IExpression _2080_collection = _source84.dtor_collection;
        bool _2081_is__forall = _source84.dtor_is__forall;
        DAST._IExpression _2082_lambda = _source84.dtor_lambda;
        unmatched84 = false;
        {
          RAST._IType _2083_tpe;
          RAST._IType _out627;
          _out627 = (this).GenType(_2079_elemType, false, false);
          _2083_tpe = _out627;
          RAST._IExpr _2084_collectionGen;
          DCOMP._IOwnership _2085___v187;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2086_recIdents;
          RAST._IExpr _out628;
          DCOMP._IOwnership _out629;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out630;
          (this).GenExpr(_2080_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out628, out _out629, out _out630);
          _2084_collectionGen = _out628;
          _2085___v187 = _out629;
          _2086_recIdents = _out630;
          Dafny.ISequence<DAST._IAttribute> _2087_extraAttributes;
          _2087_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2080_collection).is_IntRange) || ((_2080_collection).is_UnboundedIntRange)) || ((_2080_collection).is_SeqBoundedPool)) {
            _2087_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2082_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2088_formals;
            _2088_formals = (_2082_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2089_newFormals;
            _2089_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi45 = new BigInteger((_2088_formals).Count);
            for (BigInteger _2090_i = BigInteger.Zero; _2090_i < _hi45; _2090_i++) {
              var _pat_let_tv106 = _2087_extraAttributes;
              var _pat_let_tv107 = _2088_formals;
              _2089_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2089_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2088_formals).Select(_2090_i), _pat_let13_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let13_0, _2091_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv106, ((_pat_let_tv107).Select(_2090_i)).dtor_attributes), _pat_let14_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let14_0, _2092_dt__update_hattributes_h0 => DAST.Formal.create((_2091_dt__update__tmp_h0).dtor_name, (_2091_dt__update__tmp_h0).dtor_typ, _2092_dt__update_hattributes_h0)))))));
            }
            var _pat_let_tv108 = _2089_newFormals;
            DAST._IExpression _2093_newLambda;
            _2093_newLambda = Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_2082_lambda, _pat_let15_0 => Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_pat_let15_0, _2094_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let_tv108, _pat_let16_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let16_0, _2095_dt__update_hparams_h0 => DAST.Expression.create_Lambda(_2095_dt__update_hparams_h0, (_2094_dt__update__tmp_h1).dtor_retType, (_2094_dt__update__tmp_h1).dtor_body)))));
            RAST._IExpr _2096_lambdaGen;
            DCOMP._IOwnership _2097___v188;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2098_recLambdaIdents;
            RAST._IExpr _out631;
            DCOMP._IOwnership _out632;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out633;
            (this).GenExpr(_2093_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out631, out _out632, out _out633);
            _2096_lambdaGen = _out631;
            _2097___v188 = _out632;
            _2098_recLambdaIdents = _out633;
            Dafny.ISequence<Dafny.Rune> _2099_fn;
            _2099_fn = ((_2081_is__forall) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any")));
            r = ((_2084_collectionGen).Sel(_2099_fn)).Apply1(((_2096_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2086_recIdents, _2098_recLambdaIdents);
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Quantifier without an inline lambda"));
            r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
          RAST._IExpr _out634;
          DCOMP._IOwnership _out635;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out634, out _out635);
          r = _out634;
          resultingOwnership = _out635;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      BigInteger _2100_i;
      _2100_i = BigInteger.Zero;
      while ((_2100_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _2101_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _2102_m;
        RAST._IMod _out636;
        _out636 = (this).GenModule((p).Select(_2100_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2102_m = _out636;
        _2101_generated = (_2102_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_2100_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2101_generated);
        _2100_i = (_2100_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2103_i;
      _2103_i = BigInteger.Zero;
      while ((_2103_i) < (new BigInteger((fullName).Count))) {
        if ((_2103_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2103_i)));
        _2103_i = (_2103_i) + (BigInteger.One);
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
        return (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))).Clone();
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