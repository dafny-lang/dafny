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
      Dafny.ISequence<Dafny.Rune> _1040___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1040___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1040___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1040___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in123 = (i).Drop(new BigInteger(2));
        i = _in123;
        goto TAIL_CALL_START;
      } else {
        _1040___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1040___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in124 = (i).Drop(BigInteger.One);
        i = _in124;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1041___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1041___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1041___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1041___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in125 = (i).Drop(BigInteger.One);
        i = _in125;
        goto TAIL_CALL_START;
      } else {
        _1041___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1041___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _1042_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1042_r);
      }
    }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__rust { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("async"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("await"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("const"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("continue"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("crate"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("else"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("enum"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("for"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("loop"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mod"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mut"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ref"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Self"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("static"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("struct"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("trait"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("union"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsafe"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("use"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("where"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Keywords"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("The"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abstract"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("become"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("box"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("do"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("final"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("macro"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("override"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("priv"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("try"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("typeof"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsized"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("virtual"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("yield"));
    } }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__rust__need__prefix { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u8"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u16"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u32"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u64"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u128"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i8"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i16"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i32"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i64"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i128"));
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
      BigInteger _1043_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1043_indexInEnv), ((this).dtor_names).Drop((_1043_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
    }
  }

  public partial class COMP {
    public COMP() {
      this.error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.Default();
      this._UnicodeChars = false;
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> error {get; set;}
    public void __ctor(bool unicodeChars)
    {
      (this)._UnicodeChars = unicodeChars;
      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
    }
    public RAST._IMod GenModule(DAST._IModule mod, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      RAST._IMod s = RAST.Mod.Default();
      Dafny.ISequence<Dafny.Rune> _1044_modName;
      _1044_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_1044_modName);
      } else {
        Dafny.ISequence<RAST._IModDecl> _1045_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _1045_body = _out15;
        s = RAST.Mod.create_Mod(_1044_modName, _1045_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi5 = new BigInteger((body).Count);
      for (BigInteger _1046_i = BigInteger.Zero; _1046_i < _hi5; _1046_i++) {
        Dafny.ISequence<RAST._IModDecl> _1047_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source45 = (body).Select(_1046_i);
        bool unmatched45 = true;
        if (unmatched45) {
          if (_source45.is_Module) {
            DAST._IModule _1048_m = _source45.dtor_Module_a0;
            unmatched45 = false;
            RAST._IMod _1049_mm;
            RAST._IMod _out16;
            _out16 = (this).GenModule(_1048_m, containingPath);
            _1049_mm = _out16;
            _1047_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1049_mm));
          }
        }
        if (unmatched45) {
          if (_source45.is_Class) {
            DAST._IClass _1050_c = _source45.dtor_Class_a0;
            unmatched45 = false;
            Dafny.ISequence<RAST._IModDecl> _out17;
            _out17 = (this).GenClass(_1050_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1050_c).dtor_name)));
            _1047_generated = _out17;
          }
        }
        if (unmatched45) {
          if (_source45.is_Trait) {
            DAST._ITrait _1051_t = _source45.dtor_Trait_a0;
            unmatched45 = false;
            Dafny.ISequence<Dafny.Rune> _1052_tt;
            Dafny.ISequence<Dafny.Rune> _out18;
            _out18 = (this).GenTrait(_1051_t, containingPath);
            _1052_tt = _out18;
            _1047_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_RawDecl(_1052_tt));
          }
        }
        if (unmatched45) {
          if (_source45.is_Newtype) {
            DAST._INewtype _1053_n = _source45.dtor_Newtype_a0;
            unmatched45 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenNewtype(_1053_n);
            _1047_generated = _out19;
          }
        }
        if (unmatched45) {
          if (_source45.is_SynonymType) {
            DAST._ISynonymType _1054_s = _source45.dtor_SynonymType_a0;
            unmatched45 = false;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenSynonymType(_1054_s);
            _1047_generated = _out20;
          }
        }
        if (unmatched45) {
          DAST._IDatatype _1055_d = _source45.dtor_Datatype_a0;
          unmatched45 = false;
          Dafny.ISequence<RAST._IModDecl> _out21;
          _out21 = (this).GenDatatype(_1055_d);
          _1047_generated = _out21;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1047_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1056_genTpConstraint;
      _1056_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1056_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1056_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1056_genTpConstraint);
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
        for (BigInteger _1057_tpI = BigInteger.Zero; _1057_tpI < _hi6; _1057_tpI++) {
          DAST._ITypeArgDecl _1058_tp;
          _1058_tp = (@params).Select(_1057_tpI);
          DAST._IType _1059_typeArg;
          RAST._ITypeParamDecl _1060_typeParam;
          DAST._IType _out22;
          RAST._ITypeParamDecl _out23;
          (this).GenTypeParam(_1058_tp, out _out22, out _out23);
          _1059_typeArg = _out22;
          _1060_typeParam = _out23;
          RAST._IType _1061_rType;
          RAST._IType _out24;
          _out24 = (this).GenType(_1059_typeArg, false, false);
          _1061_rType = _out24;
          typeParamsSet = Dafny.Set<DAST._IType>.Union(typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1059_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1061_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1060_typeParam));
        }
      }
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1062_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1063_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1064_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1065_whereConstraints;
      Dafny.ISet<DAST._IType> _out25;
      Dafny.ISequence<RAST._IType> _out26;
      Dafny.ISequence<RAST._ITypeParamDecl> _out27;
      Dafny.ISequence<Dafny.Rune> _out28;
      (this).GenTypeParameters((c).dtor_typeParams, out _out25, out _out26, out _out27, out _out28);
      _1062_typeParamsSet = _out25;
      _1063_rTypeParams = _out26;
      _1064_rTypeParamsDecls = _out27;
      _1065_whereConstraints = _out28;
      Dafny.ISequence<Dafny.Rune> _1066_constrainedTypeParams;
      _1066_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1064_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1067_fields;
      _1067_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1068_fieldInits;
      _1068_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1069_fieldI = BigInteger.Zero; _1069_fieldI < _hi7; _1069_fieldI++) {
        DAST._IField _1070_field;
        _1070_field = ((c).dtor_fields).Select(_1069_fieldI);
        RAST._IType _1071_fieldType;
        RAST._IType _out29;
        _out29 = (this).GenType(((_1070_field).dtor_formal).dtor_typ, false, false);
        _1071_fieldType = _out29;
        Dafny.ISequence<Dafny.Rune> _1072_fieldRustName;
        _1072_fieldRustName = DCOMP.__default.escapeName(((_1070_field).dtor_formal).dtor_name);
        _1067_fields = Dafny.Sequence<RAST._IField>.Concat(_1067_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1072_fieldRustName, _1071_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source46 = (_1070_field).dtor_defaultValue;
        bool unmatched46 = true;
        if (unmatched46) {
          if (_source46.is_Some) {
            DAST._IExpression _1073_e = _source46.dtor_value;
            unmatched46 = false;
            {
              RAST._IExpr _1074_expr;
              DCOMP._IOwnership _1075___v43;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1076___v44;
              RAST._IExpr _out30;
              DCOMP._IOwnership _out31;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
              (this).GenExpr(_1073_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
              _1074_expr = _out30;
              _1075___v43 = _out31;
              _1076___v44 = _out32;
              _1068_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1068_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1070_field).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cell::RefCell::new("), (_1074_expr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))))));
            }
          }
        }
        if (unmatched46) {
          unmatched46 = false;
          {
            RAST._IExpr _1077_default;
            _1077_default = RAST.__default.std__Default__default;
            _1068_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1068_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1072_fieldRustName, _1077_default)));
          }
        }
      }
      BigInteger _hi8 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1078_typeParamI = BigInteger.Zero; _1078_typeParamI < _hi8; _1078_typeParamI++) {
        DAST._IType _1079_typeArg;
        RAST._ITypeParamDecl _1080_typeParam;
        DAST._IType _out33;
        RAST._ITypeParamDecl _out34;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1078_typeParamI), out _out33, out _out34);
        _1079_typeArg = _out33;
        _1080_typeParam = _out34;
        RAST._IType _1081_rTypeArg;
        RAST._IType _out35;
        _out35 = (this).GenType(_1079_typeArg, false, false);
        _1081_rTypeArg = _out35;
        _1067_fields = Dafny.Sequence<RAST._IField>.Concat(_1067_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1078_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1081_rTypeArg))))));
        _1068_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1068_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1078_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      Dafny.ISequence<Dafny.Rune> _1082_datatypeName;
      _1082_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IStruct _1083_struct;
      _1083_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1082_datatypeName, _1064_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1067_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1083_struct));
      Dafny.ISequence<RAST._IImplMember> _1084_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1085_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out36;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out37;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(path, (c).dtor_attributes))), _1062_typeParamsSet, out _out36, out _out37);
      _1084_implBodyRaw = _out36;
      _1085_traitBodies = _out37;
      Dafny.ISequence<RAST._IImplMember> _1086_implBody;
      _1086_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(RAST.Expr.create_Identifier(_1082_datatypeName), _1068_fieldInits))))), _1084_implBodyRaw);
      RAST._IImpl _1087_i;
      _1087_i = RAST.Impl.create_Impl(_1064_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1082_datatypeName), _1063_rTypeParams), _1065_whereConstraints, _1086_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1087_i)));
      if ((new BigInteger(((c).dtor_superClasses).Count)).Sign == 1) {
        BigInteger _1088_i;
        _1088_i = BigInteger.Zero;
        while ((_1088_i) < (new BigInteger(((c).dtor_superClasses).Count))) {
          DAST._IType _1089_superClass;
          _1089_superClass = ((c).dtor_superClasses).Select(_1088_i);
          DAST._IType _source47 = _1089_superClass;
          bool unmatched47 = true;
          if (unmatched47) {
            if (_source47.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1090_traitPath = _source47.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _1091_typeArgs = _source47.dtor_typeArgs;
              DAST._IResolvedType resolved0 = _source47.dtor_resolved;
              if (resolved0.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1092___v45 = resolved0.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1093___v46 = resolved0.dtor_attributes;
                unmatched47 = false;
                {
                  RAST._IType _1094_pathStr;
                  RAST._IType _out38;
                  _out38 = DCOMP.COMP.GenPath(_1090_traitPath);
                  _1094_pathStr = _out38;
                  Dafny.ISequence<RAST._IType> _1095_typeArgs;
                  Dafny.ISequence<RAST._IType> _out39;
                  _out39 = (this).GenTypeArgs(_1091_typeArgs, false, false);
                  _1095_typeArgs = _out39;
                  Dafny.ISequence<RAST._IImplMember> _1096_body;
                  _1096_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((_1085_traitBodies).Contains(_1090_traitPath)) {
                    _1096_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1085_traitBodies,_1090_traitPath);
                  }
                  RAST._IType _1097_genSelfPath;
                  RAST._IType _out40;
                  _out40 = DCOMP.COMP.GenPath(path);
                  _1097_genSelfPath = _out40;
                  RAST._IModDecl _1098_x;
                  _1098_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1064_rTypeParamsDecls, RAST.Type.create_TypeApp(_1094_pathStr, _1095_typeArgs), RAST.__default.Rc(RAST.Type.create_TypeApp(_1097_genSelfPath, _1063_rTypeParams)), _1065_whereConstraints, _1096_body));
                  s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1098_x));
                }
              }
            }
          }
          if (unmatched47) {
            DAST._IType _1099___v47 = _source47;
            unmatched47 = false;
          }
          _1088_i = (_1088_i) + (BigInteger.One);
        }
      }
      RAST._IImpl _1100_d;
      _1100_d = RAST.Impl.create_ImplFor(_1064_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1082_datatypeName), _1063_rTypeParams), _1065_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(_1082_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new()"))))))));
      Dafny.ISequence<RAST._IModDecl> _1101_defaultImpl;
      _1101_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1100_d));
      RAST._IImpl _1102_p;
      _1102_p = RAST.Impl.create_ImplFor(_1064_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1082_datatypeName), _1063_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), DCOMP.__default.escapeName(((c).dtor_enclosingModule))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")"))))))));
      Dafny.ISequence<RAST._IModDecl> _1103_printImpl;
      _1103_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1102_p));
      RAST._IImpl _1104_pp;
      _1104_pp = RAST.Impl.create_ImplFor(_1064_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cmp::PartialEq")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1082_datatypeName), _1063_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("eq"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.__default.SelfBorrowed)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ptr::eq(self, other)")))))));
      Dafny.ISequence<RAST._IModDecl> _1105_ptrPartialEqImpl;
      _1105_ptrPartialEqImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1104_pp));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(s, _1101_defaultImpl), _1103_printImpl), _1105_ptrPartialEqImpl);
      return s;
    }
    public Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _1106_typeParamsSet;
      _1106_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1107_typeParamDecls;
      _1107_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1108_typeParams;
      _1108_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1109_tpI;
      _1109_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        while ((_1109_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._ITypeArgDecl _1110_tp;
          _1110_tp = ((t).dtor_typeParams).Select(_1109_tpI);
          DAST._IType _1111_typeArg;
          RAST._ITypeParamDecl _1112_typeParamDecl;
          DAST._IType _out41;
          RAST._ITypeParamDecl _out42;
          (this).GenTypeParam(_1110_tp, out _out41, out _out42);
          _1111_typeArg = _out41;
          _1112_typeParamDecl = _out42;
          _1106_typeParamsSet = Dafny.Set<DAST._IType>.Union(_1106_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1111_typeArg));
          _1107_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1107_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1112_typeParamDecl));
          RAST._IType _1113_typeParam;
          RAST._IType _out43;
          _out43 = (this).GenType(_1111_typeArg, false, false);
          _1113_typeParam = _out43;
          _1108_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1108_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1113_typeParam));
          _1109_tpI = (_1109_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1114_fullPath;
      _1114_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1115_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1116___v48;
      Dafny.ISequence<RAST._IImplMember> _out44;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out45;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_1114_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_1114_fullPath, (t).dtor_attributes)), _1106_typeParamsSet, out _out44, out _out45);
      _1115_implBody = _out44;
      _1116___v48 = _out45;
      s = (RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1107_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1108_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1115_implBody)))._ToString(DCOMP.__default.IND);
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1117_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1118_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1119_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1120_whereConstraints;
      Dafny.ISet<DAST._IType> _out46;
      Dafny.ISequence<RAST._IType> _out47;
      Dafny.ISequence<RAST._ITypeParamDecl> _out48;
      Dafny.ISequence<Dafny.Rune> _out49;
      (this).GenTypeParameters((c).dtor_typeParams, out _out46, out _out47, out _out48, out _out49);
      _1117_typeParamsSet = _out46;
      _1118_rTypeParams = _out47;
      _1119_rTypeParamsDecls = _out48;
      _1120_whereConstraints = _out49;
      Dafny.ISequence<Dafny.Rune> _1121_constrainedTypeParams;
      _1121_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1119_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1122_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source48 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      bool unmatched48 = true;
      if (unmatched48) {
        if (_source48.is_Some) {
          RAST._IType _1123_v = _source48.dtor_value;
          unmatched48 = false;
          _1122_underlyingType = _1123_v;
        }
      }
      if (unmatched48) {
        unmatched48 = false;
        RAST._IType _out50;
        _out50 = (this).GenType((c).dtor_base, false, false);
        _1122_underlyingType = _out50;
      }
      DAST._IType _1124_resultingType;
      _1124_resultingType = DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Newtype((c).dtor_base, (c).dtor_range, false, (c).dtor_attributes));
      Dafny.ISequence<Dafny.Rune> _1125_datatypeName;
      _1125_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1125_datatypeName, _1119_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1122_underlyingType))))));
      RAST._IExpr _1126_fnBody;
      _1126_fnBody = RAST.Expr.create_Identifier(_1125_datatypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source49 = (c).dtor_witnessExpr;
      bool unmatched49 = true;
      if (unmatched49) {
        if (_source49.is_Some) {
          DAST._IExpression _1127_e = _source49.dtor_value;
          unmatched49 = false;
          {
            DAST._IExpression _1128_e;
            _1128_e = ((object.Equals((c).dtor_base, _1124_resultingType)) ? (_1127_e) : (DAST.Expression.create_Convert(_1127_e, (c).dtor_base, _1124_resultingType)));
            RAST._IExpr _1129_eStr;
            DCOMP._IOwnership _1130___v49;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1131___v50;
            RAST._IExpr _out51;
            DCOMP._IOwnership _out52;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out53;
            (this).GenExpr(_1128_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out51, out _out52, out _out53);
            _1129_eStr = _out51;
            _1130___v49 = _out52;
            _1131___v50 = _out53;
            _1126_fnBody = (_1126_fnBody).Apply1(_1129_eStr);
          }
        }
      }
      if (unmatched49) {
        unmatched49 = false;
        {
          _1126_fnBody = (_1126_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1132_body;
      _1132_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1126_fnBody)));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1119_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1125_datatypeName), _1118_rTypeParams), _1120_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1132_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1119_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1125_datatypeName), _1118_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1119_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1125_datatypeName), _1118_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1122_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1133_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1134_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1135_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1136_whereConstraints;
      Dafny.ISet<DAST._IType> _out54;
      Dafny.ISequence<RAST._IType> _out55;
      Dafny.ISequence<RAST._ITypeParamDecl> _out56;
      Dafny.ISequence<Dafny.Rune> _out57;
      (this).GenTypeParameters((c).dtor_typeParams, out _out54, out _out55, out _out56, out _out57);
      _1133_typeParamsSet = _out54;
      _1134_rTypeParams = _out55;
      _1135_rTypeParamsDecls = _out56;
      _1136_whereConstraints = _out57;
      Dafny.ISequence<Dafny.Rune> _1137_constrainedTypeParams;
      _1137_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1135_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<Dafny.Rune> _1138_synonymTypeName;
      _1138_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _1139_resultingType;
      RAST._IType _out58;
      _out58 = (this).GenType((c).dtor_base, false, false);
      _1139_resultingType = _out58;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1138_synonymTypeName, _1135_rTypeParamsDecls, _1139_resultingType)));
      Std.Wrappers._IOption<DAST._IExpression> _source50 = (c).dtor_witnessExpr;
      bool unmatched50 = true;
      if (unmatched50) {
        if (_source50.is_Some) {
          DAST._IExpression _1140_e = _source50.dtor_value;
          unmatched50 = false;
          {
            RAST._IExpr _1141_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1142___v51;
            DCOMP._IEnvironment _1143_newEnv;
            RAST._IExpr _out59;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out60;
            DCOMP._IEnvironment _out61;
            (this).GenStmts((c).dtor_witnessStmts, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), false, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out59, out _out60, out _out61);
            _1141_rStmts = _out59;
            _1142___v51 = _out60;
            _1143_newEnv = _out61;
            RAST._IExpr _1144_rExpr;
            DCOMP._IOwnership _1145___v52;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1146___v53;
            RAST._IExpr _out62;
            DCOMP._IOwnership _out63;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out64;
            (this).GenExpr(_1140_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), _1143_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out62, out _out63, out _out64);
            _1144_rExpr = _out62;
            _1145___v52 = _out63;
            _1146___v53 = _out64;
            Dafny.ISequence<Dafny.Rune> _1147_constantName;
            _1147_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_1147_constantName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1139_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_1141_rStmts).Then(_1144_rExpr)))))));
          }
        }
      }
      if (unmatched50) {
        unmatched50 = false;
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1148_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1149_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1150_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1151_whereConstraints;
      Dafny.ISet<DAST._IType> _out65;
      Dafny.ISequence<RAST._IType> _out66;
      Dafny.ISequence<RAST._ITypeParamDecl> _out67;
      Dafny.ISequence<Dafny.Rune> _out68;
      (this).GenTypeParameters((c).dtor_typeParams, out _out65, out _out66, out _out67, out _out68);
      _1148_typeParamsSet = _out65;
      _1149_rTypeParams = _out66;
      _1150_rTypeParamsDecls = _out67;
      _1151_whereConstraints = _out68;
      Dafny.ISequence<Dafny.Rune> _1152_datatypeName;
      _1152_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1153_ctors;
      _1153_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      BigInteger _hi9 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1154_i = BigInteger.Zero; _1154_i < _hi9; _1154_i++) {
        DAST._IDatatypeCtor _1155_ctor;
        _1155_ctor = ((c).dtor_ctors).Select(_1154_i);
        Dafny.ISequence<RAST._IField> _1156_ctorArgs;
        _1156_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1157_isNumeric;
        _1157_isNumeric = false;
        BigInteger _hi10 = new BigInteger(((_1155_ctor).dtor_args).Count);
        for (BigInteger _1158_j = BigInteger.Zero; _1158_j < _hi10; _1158_j++) {
          DAST._IDatatypeDtor _1159_dtor;
          _1159_dtor = ((_1155_ctor).dtor_args).Select(_1158_j);
          RAST._IType _1160_formalType;
          RAST._IType _out69;
          _out69 = (this).GenType(((_1159_dtor).dtor_formal).dtor_typ, false, false);
          _1160_formalType = _out69;
          Dafny.ISequence<Dafny.Rune> _1161_formalName;
          _1161_formalName = DCOMP.__default.escapeName(((_1159_dtor).dtor_formal).dtor_name);
          if (((_1158_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1161_formalName))) {
            _1157_isNumeric = true;
          }
          if ((((_1158_j).Sign != 0) && (_1157_isNumeric)) && (!(Std.Strings.__default.OfNat(_1158_j)).Equals(_1161_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1161_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1158_j)));
            _1157_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1156_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1156_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1161_formalName, RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1160_formalType))))));
          } else {
            _1156_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1156_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1161_formalName, _1160_formalType))));
          }
        }
        RAST._IFields _1162_namedFields;
        _1162_namedFields = RAST.Fields.create_NamedFields(_1156_ctorArgs);
        if (_1157_isNumeric) {
          _1162_namedFields = (_1162_namedFields).ToNamelessFields();
        }
        _1153_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1153_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1155_ctor).dtor_name), _1162_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1163_selfPath;
      _1163_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1164_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1165_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out70;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out71;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(_1163_selfPath, (c).dtor_attributes))), _1148_typeParamsSet, out _out70, out _out71);
      _1164_implBodyRaw = _out70;
      _1165_traitBodies = _out71;
      Dafny.ISequence<RAST._IImplMember> _1166_implBody;
      _1166_implBody = _1164_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1167_emittedFields;
      _1167_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi11 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1168_i = BigInteger.Zero; _1168_i < _hi11; _1168_i++) {
        DAST._IDatatypeCtor _1169_ctor;
        _1169_ctor = ((c).dtor_ctors).Select(_1168_i);
        BigInteger _hi12 = new BigInteger(((_1169_ctor).dtor_args).Count);
        for (BigInteger _1170_j = BigInteger.Zero; _1170_j < _hi12; _1170_j++) {
          DAST._IDatatypeDtor _1171_dtor;
          _1171_dtor = ((_1169_ctor).dtor_args).Select(_1170_j);
          Dafny.ISequence<Dafny.Rune> _1172_callName;
          _1172_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1171_dtor).dtor_callName, DCOMP.__default.escapeName(((_1171_dtor).dtor_formal).dtor_name));
          if (!((_1167_emittedFields).Contains(_1172_callName))) {
            _1167_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1167_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1172_callName));
            RAST._IType _1173_formalType;
            RAST._IType _out72;
            _out72 = (this).GenType(((_1171_dtor).dtor_formal).dtor_typ, false, false);
            _1173_formalType = _out72;
            Dafny.ISequence<RAST._IMatchCase> _1174_cases;
            _1174_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1175_k = BigInteger.Zero; _1175_k < _hi13; _1175_k++) {
              DAST._IDatatypeCtor _1176_ctor2;
              _1176_ctor2 = ((c).dtor_ctors).Select(_1175_k);
              Dafny.ISequence<Dafny.Rune> _1177_pattern;
              _1177_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1152_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1176_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1178_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1179_hasMatchingField;
              _1179_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1180_patternInner;
              _1180_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1181_isNumeric;
              _1181_isNumeric = false;
              BigInteger _hi14 = new BigInteger(((_1176_ctor2).dtor_args).Count);
              for (BigInteger _1182_l = BigInteger.Zero; _1182_l < _hi14; _1182_l++) {
                DAST._IDatatypeDtor _1183_dtor2;
                _1183_dtor2 = ((_1176_ctor2).dtor_args).Select(_1182_l);
                Dafny.ISequence<Dafny.Rune> _1184_patternName;
                _1184_patternName = DCOMP.__default.escapeName(((_1183_dtor2).dtor_formal).dtor_name);
                if (((_1182_l).Sign == 0) && ((_1184_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1181_isNumeric = true;
                }
                if (_1181_isNumeric) {
                  _1184_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1183_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1182_l)));
                }
                if (object.Equals(((_1171_dtor).dtor_formal).dtor_name, ((_1183_dtor2).dtor_formal).dtor_name)) {
                  _1179_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1184_patternName);
                }
                _1180_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1180_patternInner, _1184_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1181_isNumeric) {
                _1177_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1177_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1180_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1177_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1177_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1180_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1179_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1178_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1179_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1178_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1179_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1178_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _1185_ctorMatch;
              _1185_ctorMatch = RAST.MatchCase.create(_1177_pattern, RAST.Expr.create_RawExpr(_1178_rhs));
              _1174_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1174_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1185_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1174_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1174_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1152_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _1186_methodBody;
            _1186_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1174_cases);
            _1166_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1166_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1172_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1173_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1186_methodBody)))));
          }
        }
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1187_types;
        _1187_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi15 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1188_typeI = BigInteger.Zero; _1188_typeI < _hi15; _1188_typeI++) {
          DAST._IType _1189_typeArg;
          RAST._ITypeParamDecl _1190_rTypeParamDecl;
          DAST._IType _out73;
          RAST._ITypeParamDecl _out74;
          (this).GenTypeParam(((c).dtor_typeParams).Select(_1188_typeI), out _out73, out _out74);
          _1189_typeArg = _out73;
          _1190_rTypeParamDecl = _out74;
          RAST._IType _1191_rTypeArg;
          RAST._IType _out75;
          _out75 = (this).GenType(_1189_typeArg, false, false);
          _1191_rTypeArg = _out75;
          _1187_types = Dafny.Sequence<RAST._IType>.Concat(_1187_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1191_rTypeArg))));
        }
        _1153_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1153_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1192_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1192_tpe);
})), _1187_types)))));
      }
      Dafny.ISequence<RAST._IModDecl> _1193_enumBody;
      _1193_enumBody = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]")), _1152_datatypeName, _1150_rTypeParamsDecls, _1153_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1150_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1152_datatypeName), _1149_rTypeParams), _1151_whereConstraints, _1166_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1194_printImplBodyCases;
      _1194_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1195_i = BigInteger.Zero; _1195_i < _hi16; _1195_i++) {
        DAST._IDatatypeCtor _1196_ctor;
        _1196_ctor = ((c).dtor_ctors).Select(_1195_i);
        Dafny.ISequence<Dafny.Rune> _1197_ctorMatch;
        _1197_ctorMatch = DCOMP.__default.escapeName((_1196_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1198_modulePrefix;
        _1198_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1199_ctorName;
        _1199_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1198_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1196_ctor).dtor_name));
        if (((new BigInteger((_1199_ctorName).Count)) >= (new BigInteger(13))) && (((_1199_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1199_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1200_printRhs;
        _1200_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1199_ctorName), (((_1196_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        bool _1201_isNumeric;
        _1201_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1202_ctorMatchInner;
        _1202_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi17 = new BigInteger(((_1196_ctor).dtor_args).Count);
        for (BigInteger _1203_j = BigInteger.Zero; _1203_j < _hi17; _1203_j++) {
          DAST._IDatatypeDtor _1204_dtor;
          _1204_dtor = ((_1196_ctor).dtor_args).Select(_1203_j);
          Dafny.ISequence<Dafny.Rune> _1205_patternName;
          _1205_patternName = DCOMP.__default.escapeName(((_1204_dtor).dtor_formal).dtor_name);
          if (((_1203_j).Sign == 0) && ((_1205_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1201_isNumeric = true;
          }
          if (_1201_isNumeric) {
            _1205_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1204_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1203_j)));
          }
          _1202_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1202_ctorMatchInner, _1205_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1203_j).Sign == 1) {
            _1200_printRhs = (_1200_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1200_printRhs = (_1200_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1205_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))));
        }
        if (_1201_isNumeric) {
          _1197_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1197_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1202_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1197_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1197_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1202_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1196_ctor).dtor_hasAnyArgs) {
          _1200_printRhs = (_1200_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1200_printRhs = (_1200_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1194_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1194_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1152_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1197_ctorMatch), RAST.Expr.create_Block(_1200_printRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _1194_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1194_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1152_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1206_defaultConstrainedTypeParams;
      _1206_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1150_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      RAST._IExpr _1207_printImplBody;
      _1207_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1194_printImplBodyCases);
      Dafny.ISequence<RAST._IModDecl> _1208_printImpl;
      _1208_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1150_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1152_datatypeName), _1149_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1150_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1152_datatypeName), _1149_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1207_printImplBody)))))));
      Dafny.ISequence<RAST._IModDecl> _1209_defaultImpl;
      _1209_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      Dafny.ISequence<RAST._IModDecl> _1210_asRefImpl;
      _1210_asRefImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1211_structName;
        _1211_structName = (RAST.Expr.create_Identifier(_1152_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1212_structAssignments;
        _1212_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi18 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1213_i = BigInteger.Zero; _1213_i < _hi18; _1213_i++) {
          DAST._IDatatypeDtor _1214_dtor;
          _1214_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1213_i);
          _1212_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1212_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1214_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1215_defaultConstrainedTypeParams;
        _1215_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1150_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1216_fullType;
        _1216_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1152_datatypeName), _1149_rTypeParams);
        _1209_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1215_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1216_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1216_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1211_structName, _1212_structAssignments))))))));
        _1210_asRefImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1150_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_1216_fullType), RAST.Type.create_Borrowed(_1216_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self)))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(_1193_enumBody, _1208_printImpl), _1209_defaultImpl), _1210_asRefImpl);
      return s;
    }
    public static RAST._IType GenPath(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p)
    {
      RAST._IType r = RAST.Type.Default();
      if ((new BigInteger((p).Count)).Sign == 0) {
        r = RAST.Type.create_SelfOwned();
        return r;
      } else {
        r = ((((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))) ? (RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) : (RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"))));
        BigInteger _hi19 = new BigInteger((p).Count);
        for (BigInteger _1217_i = BigInteger.Zero; _1217_i < _hi19; _1217_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1217_i))));
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
        r = ((((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))) ? (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) : (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"))));
        BigInteger _hi20 = new BigInteger((p).Count);
        for (BigInteger _1218_i = BigInteger.Zero; _1218_i < _hi20; _1218_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1218_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding, bool inFn)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger((args).Count)).Sign == 1) {
        BigInteger _1219_i;
        _1219_i = BigInteger.Zero;
        while ((_1219_i) < (new BigInteger((args).Count))) {
          RAST._IType _1220_genTp;
          RAST._IType _out76;
          _out76 = (this).GenType((args).Select(_1219_i), inBinding, inFn);
          _1220_genTp = _out76;
          s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1220_genTp));
          _1219_i = (_1219_i) + (BigInteger.One);
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
      DAST._IType _source51 = c;
      bool unmatched51 = true;
      if (unmatched51) {
        if (_source51.is_Path) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1221_p = _source51.dtor_Path_a0;
          Dafny.ISequence<DAST._IType> _1222_args = _source51.dtor_typeArgs;
          DAST._IResolvedType _1223_resolved = _source51.dtor_resolved;
          unmatched51 = false;
          {
            RAST._IType _1224_t;
            RAST._IType _out77;
            _out77 = DCOMP.COMP.GenPath(_1221_p);
            _1224_t = _out77;
            Dafny.ISequence<RAST._IType> _1225_typeArgs;
            Dafny.ISequence<RAST._IType> _out78;
            _out78 = (this).GenTypeArgs(_1222_args, inBinding, inFn);
            _1225_typeArgs = _out78;
            s = RAST.Type.create_TypeApp(_1224_t, _1225_typeArgs);
            DAST._IResolvedType _source52 = _1223_resolved;
            bool unmatched52 = true;
            if (unmatched52) {
              if (_source52.is_Datatype) {
                DAST._IDatatypeType datatypeType0 = _source52.dtor_datatypeType;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1226___v54 = datatypeType0.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1227_attributes = datatypeType0.dtor_attributes;
                unmatched52 = false;
                {
                  if ((this).IsRcWrapped(_1227_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched52) {
              if (_source52.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1228___v55 = _source52.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1229___v56 = _source52.dtor_attributes;
                unmatched52 = false;
                {
                  if ((_1221_p).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc<dyn ::std::any::Any>"));
                  } else {
                    if (inBinding) {
                      s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
                    } else {
                      s = RAST.Type.create_ImplType(s);
                    }
                  }
                }
              }
            }
            if (unmatched52) {
              DAST._IType _1230_t = _source52.dtor_baseType;
              DAST._INewtypeRange _1231_range = _source52.dtor_range;
              bool _1232_erased = _source52.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1233_attributes = _source52.dtor_attributes;
              unmatched52 = false;
              {
                if (_1232_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source53 = DCOMP.COMP.NewtypeToRustType(_1230_t, _1231_range);
                  bool unmatched53 = true;
                  if (unmatched53) {
                    if (_source53.is_Some) {
                      RAST._IType _1234_v = _source53.dtor_value;
                      unmatched53 = false;
                      s = _1234_v;
                    }
                  }
                  if (unmatched53) {
                    unmatched53 = false;
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched51) {
        if (_source51.is_Nullable) {
          DAST._IType _1235_inner = _source51.dtor_Nullable_a0;
          unmatched51 = false;
          {
            RAST._IType _1236_innerExpr;
            RAST._IType _out79;
            _out79 = (this).GenType(_1235_inner, inBinding, inFn);
            _1236_innerExpr = _out79;
            s = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::option::Option")), Dafny.Sequence<RAST._IType>.FromElements(_1236_innerExpr));
          }
        }
      }
      if (unmatched51) {
        if (_source51.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1237_types = _source51.dtor_Tuple_a0;
          unmatched51 = false;
          {
            Dafny.ISequence<RAST._IType> _1238_args;
            _1238_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1239_i;
            _1239_i = BigInteger.Zero;
            while ((_1239_i) < (new BigInteger((_1237_types).Count))) {
              RAST._IType _1240_generated;
              RAST._IType _out80;
              _out80 = (this).GenType((_1237_types).Select(_1239_i), inBinding, inFn);
              _1240_generated = _out80;
              _1238_args = Dafny.Sequence<RAST._IType>.Concat(_1238_args, Dafny.Sequence<RAST._IType>.FromElements(_1240_generated));
              _1239_i = (_1239_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1237_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1238_args)) : (RAST.__default.SystemTupleType(_1238_args)));
          }
        }
      }
      if (unmatched51) {
        if (_source51.is_Array) {
          DAST._IType _1241_element = _source51.dtor_element;
          BigInteger _1242_dims = _source51.dtor_dims;
          unmatched51 = false;
          {
            RAST._IType _1243_elem;
            RAST._IType _out81;
            _out81 = (this).GenType(_1241_element, inBinding, inFn);
            _1243_elem = _out81;
            s = _1243_elem;
            BigInteger _1244_i;
            _1244_i = BigInteger.Zero;
            while ((_1244_i) < (_1242_dims)) {
              s = RAST.__default.Rc(RAST.__default.RefCell(RAST.__default.Vec(s)));
              _1244_i = (_1244_i) + (BigInteger.One);
            }
          }
        }
      }
      if (unmatched51) {
        if (_source51.is_Seq) {
          DAST._IType _1245_element = _source51.dtor_element;
          unmatched51 = false;
          {
            RAST._IType _1246_elem;
            RAST._IType _out82;
            _out82 = (this).GenType(_1245_element, inBinding, inFn);
            _1246_elem = _out82;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1246_elem));
          }
        }
      }
      if (unmatched51) {
        if (_source51.is_Set) {
          DAST._IType _1247_element = _source51.dtor_element;
          unmatched51 = false;
          {
            RAST._IType _1248_elem;
            RAST._IType _out83;
            _out83 = (this).GenType(_1247_element, inBinding, inFn);
            _1248_elem = _out83;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1248_elem));
          }
        }
      }
      if (unmatched51) {
        if (_source51.is_Multiset) {
          DAST._IType _1249_element = _source51.dtor_element;
          unmatched51 = false;
          {
            RAST._IType _1250_elem;
            RAST._IType _out84;
            _out84 = (this).GenType(_1249_element, inBinding, inFn);
            _1250_elem = _out84;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1250_elem));
          }
        }
      }
      if (unmatched51) {
        if (_source51.is_Map) {
          DAST._IType _1251_key = _source51.dtor_key;
          DAST._IType _1252_value = _source51.dtor_value;
          unmatched51 = false;
          {
            RAST._IType _1253_keyType;
            RAST._IType _out85;
            _out85 = (this).GenType(_1251_key, inBinding, inFn);
            _1253_keyType = _out85;
            RAST._IType _1254_valueType;
            RAST._IType _out86;
            _out86 = (this).GenType(_1252_value, inBinding, inFn);
            _1254_valueType = _out86;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1253_keyType, _1254_valueType));
          }
        }
      }
      if (unmatched51) {
        if (_source51.is_MapBuilder) {
          DAST._IType _1255_key = _source51.dtor_key;
          DAST._IType _1256_value = _source51.dtor_value;
          unmatched51 = false;
          {
            RAST._IType _1257_keyType;
            RAST._IType _out87;
            _out87 = (this).GenType(_1255_key, inBinding, inFn);
            _1257_keyType = _out87;
            RAST._IType _1258_valueType;
            RAST._IType _out88;
            _out88 = (this).GenType(_1256_value, inBinding, inFn);
            _1258_valueType = _out88;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1257_keyType, _1258_valueType));
          }
        }
      }
      if (unmatched51) {
        if (_source51.is_SetBuilder) {
          DAST._IType _1259_elem = _source51.dtor_element;
          unmatched51 = false;
          {
            RAST._IType _1260_elemType;
            RAST._IType _out89;
            _out89 = (this).GenType(_1259_elem, inBinding, inFn);
            _1260_elemType = _out89;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1260_elemType));
          }
        }
      }
      if (unmatched51) {
        if (_source51.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1261_args = _source51.dtor_args;
          DAST._IType _1262_result = _source51.dtor_result;
          unmatched51 = false;
          {
            Dafny.ISequence<RAST._IType> _1263_argTypes;
            _1263_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1264_i;
            _1264_i = BigInteger.Zero;
            while ((_1264_i) < (new BigInteger((_1261_args).Count))) {
              RAST._IType _1265_generated;
              RAST._IType _out90;
              _out90 = (this).GenType((_1261_args).Select(_1264_i), inBinding, true);
              _1265_generated = _out90;
              _1263_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1263_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1265_generated)));
              _1264_i = (_1264_i) + (BigInteger.One);
            }
            RAST._IType _1266_resultType;
            RAST._IType _out91;
            _out91 = (this).GenType(_1262_result, inBinding, (inFn) || (inBinding));
            _1266_resultType = _out91;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1263_argTypes, _1266_resultType)));
          }
        }
      }
      if (unmatched51) {
        if (_source51.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h110 = _source51.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1267_name = _h110;
          unmatched51 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1267_name));
        }
      }
      if (unmatched51) {
        if (_source51.is_Primitive) {
          DAST._IPrimitive _1268_p = _source51.dtor_Primitive_a0;
          unmatched51 = false;
          {
            DAST._IPrimitive _source54 = _1268_p;
            bool unmatched54 = true;
            if (unmatched54) {
              if (_source54.is_Int) {
                unmatched54 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
              }
            }
            if (unmatched54) {
              if (_source54.is_Real) {
                unmatched54 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
              }
            }
            if (unmatched54) {
              if (_source54.is_String) {
                unmatched54 = false;
                s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
              }
            }
            if (unmatched54) {
              if (_source54.is_Bool) {
                unmatched54 = false;
                s = RAST.Type.create_Bool();
              }
            }
            if (unmatched54) {
              unmatched54 = false;
              s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
            }
          }
        }
      }
      if (unmatched51) {
        Dafny.ISequence<Dafny.Rune> _1269_v = _source51.dtor_Passthrough_a0;
        unmatched51 = false;
        s = RAST.__default.RawType(_1269_v);
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
      for (BigInteger _1270_i = BigInteger.Zero; _1270_i < _hi21; _1270_i++) {
        DAST._IMethod _source55 = (body).Select(_1270_i);
        bool unmatched55 = true;
        if (unmatched55) {
          DAST._IMethod _1271_m = _source55;
          unmatched55 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source56 = (_1271_m).dtor_overridingPath;
            bool unmatched56 = true;
            if (unmatched56) {
              if (_source56.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1272_p = _source56.dtor_value;
                unmatched56 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1273_existing;
                  _1273_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1272_p)) {
                    _1273_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1272_p);
                  }
                  RAST._IImplMember _1274_genMethod;
                  RAST._IImplMember _out92;
                  _out92 = (this).GenMethod(_1271_m, true, enclosingType, enclosingTypeParams);
                  _1274_genMethod = _out92;
                  _1273_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1273_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1274_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1272_p, _1273_existing)));
                }
              }
            }
            if (unmatched56) {
              unmatched56 = false;
              {
                RAST._IImplMember _1275_generated;
                RAST._IImplMember _out93;
                _out93 = (this).GenMethod(_1271_m, forTrait, enclosingType, enclosingTypeParams);
                _1275_generated = _out93;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1275_generated));
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
      for (BigInteger _1276_i = BigInteger.Zero; _1276_i < _hi22; _1276_i++) {
        DAST._IFormal _1277_param;
        _1277_param = (@params).Select(_1276_i);
        RAST._IType _1278_paramType;
        RAST._IType _out94;
        _out94 = (this).GenType((_1277_param).dtor_typ, false, false);
        _1278_paramType = _out94;
        if ((!((_1278_paramType).CanReadWithoutClone())) && (!((_1277_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1278_paramType = RAST.Type.create_Borrowed(_1278_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_1277_param).dtor_name), _1278_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1279_params;
      Dafny.ISequence<RAST._IFormal> _out95;
      _out95 = (this).GenParams((m).dtor_params);
      _1279_params = _out95;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1280_paramNames;
      _1280_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1281_paramTypes;
      _1281_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi23 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1282_paramI = BigInteger.Zero; _1282_paramI < _hi23; _1282_paramI++) {
        DAST._IFormal _1283_dafny__formal;
        _1283_dafny__formal = ((m).dtor_params).Select(_1282_paramI);
        RAST._IFormal _1284_formal;
        _1284_formal = (_1279_params).Select(_1282_paramI);
        Dafny.ISequence<Dafny.Rune> _1285_name;
        _1285_name = (_1284_formal).dtor_name;
        _1280_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1280_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1285_name));
        _1281_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1281_paramTypes, _1285_name, (_1284_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1286_fnName;
      _1286_fnName = DCOMP.__default.escapeName((m).dtor_name);
      Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1287_selfIdentifier;
      _1287_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1288_selfId;
        _1288_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((_1286_fnName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_ctor"))) {
          _1288_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        if (forTrait) {
          RAST._IFormal _1289_selfFormal;
          _1289_selfFormal = RAST.Formal.selfBorrowedMut;
          _1279_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1289_selfFormal), _1279_params);
        } else {
          RAST._IType _1290_tpe;
          RAST._IType _out96;
          _out96 = (this).GenType(enclosingType, false, false);
          _1290_tpe = _out96;
          if (!((_1290_tpe).CanReadWithoutClone())) {
            _1290_tpe = RAST.Type.create_Borrowed(_1290_tpe);
          }
          _1279_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1288_selfId, _1290_tpe)), _1279_params);
        }
        _1287_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1288_selfId);
      }
      Dafny.ISequence<RAST._IType> _1291_retTypeArgs;
      _1291_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1292_typeI;
      _1292_typeI = BigInteger.Zero;
      while ((_1292_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1293_typeExpr;
        RAST._IType _out97;
        _out97 = (this).GenType(((m).dtor_outTypes).Select(_1292_typeI), false, false);
        _1293_typeExpr = _out97;
        _1291_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1291_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1293_typeExpr));
        _1292_typeI = (_1292_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1294_visibility;
      _1294_visibility = RAST.Visibility.create_PUB();
      Dafny.ISequence<DAST._ITypeArgDecl> _1295_typeParamsFiltered;
      _1295_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi24 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1296_typeParamI = BigInteger.Zero; _1296_typeParamI < _hi24; _1296_typeParamI++) {
        DAST._ITypeArgDecl _1297_typeParam;
        _1297_typeParam = ((m).dtor_typeParams).Select(_1296_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1297_typeParam).dtor_name)))) {
          _1295_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1295_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1297_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1298_typeParams;
      _1298_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1295_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi25 = new BigInteger((_1295_typeParamsFiltered).Count);
        for (BigInteger _1299_i = BigInteger.Zero; _1299_i < _hi25; _1299_i++) {
          DAST._IType _1300_typeArg;
          RAST._ITypeParamDecl _1301_rTypeParamDecl;
          DAST._IType _out98;
          RAST._ITypeParamDecl _out99;
          (this).GenTypeParam((_1295_typeParamsFiltered).Select(_1299_i), out _out98, out _out99);
          _1300_typeArg = _out98;
          _1301_rTypeParamDecl = _out99;
          var _pat_let_tv101 = _1301_rTypeParamDecl;
          _1301_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1301_rTypeParamDecl, _pat_let6_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let6_0, _1302_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Dafny.Sequence<RAST._IType>.Concat((_pat_let_tv101).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default")))), _pat_let7_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let7_0, _1303_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1302_dt__update__tmp_h0).dtor_content, _1303_dt__update_hconstraints_h0)))));
          _1298_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1298_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1301_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1304_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1305_env = DCOMP.Environment.Default();
      RAST._IExpr _1306_preBody;
      _1306_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      if ((m).dtor_hasBody) {
        RAST._IExpr _1307_earlyReturn;
        _1307_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source57 = (m).dtor_outVars;
        bool unmatched57 = true;
        if (unmatched57) {
          if (_source57.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1308_outVars = _source57.dtor_value;
            unmatched57 = false;
            {
              Dafny.ISequence<RAST._IExpr> _1309_tupleArgs;
              _1309_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi26 = new BigInteger((_1308_outVars).Count);
              for (BigInteger _1310_outI = BigInteger.Zero; _1310_outI < _hi26; _1310_outI++) {
                Dafny.ISequence<Dafny.Rune> _1311_outVar;
                _1311_outVar = (_1308_outVars).Select(_1310_outI);
                RAST._IType _1312_outType;
                RAST._IType _out100;
                _out100 = (this).GenType(((m).dtor_outTypes).Select(_1310_outI), false, false);
                _1312_outType = _out100;
                Dafny.ISequence<Dafny.Rune> _1313_outName;
                _1313_outName = DCOMP.__default.escapeName((_1311_outVar));
                _1280_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1280_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1313_outName));
                RAST._IType _1314_outMaybeType;
                _1314_outMaybeType = (((_1312_outType).CanReadWithoutClone()) ? (_1312_outType) : (RAST.__default.MaybePlaceboType(_1312_outType)));
                _1281_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1281_paramTypes, _1313_outName, _1314_outMaybeType);
                RAST._IExpr _1315_outVarReturn;
                DCOMP._IOwnership _1316___v57;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1317___v58;
                RAST._IExpr _out101;
                DCOMP._IOwnership _out102;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out103;
                (this).GenExpr(DAST.Expression.create_Ident((_1311_outVar)), Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1313_outName), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>, RAST._IType>(_1313_outName, _1314_outMaybeType))), DCOMP.Ownership.create_OwnershipOwned(), out _out101, out _out102, out _out103);
                _1315_outVarReturn = _out101;
                _1316___v57 = _out102;
                _1317___v58 = _out103;
                _1309_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1309_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1315_outVarReturn));
              }
              if ((new BigInteger((_1309_tupleArgs).Count)) == (BigInteger.One)) {
                _1307_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1309_tupleArgs).Select(BigInteger.Zero)));
              } else {
                _1307_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1309_tupleArgs)));
              }
            }
          }
        }
        if (unmatched57) {
          unmatched57 = false;
        }
        _1305_env = DCOMP.Environment.create(_1280_paramNames, _1281_paramTypes);
        RAST._IExpr _1318_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1319___v59;
        DCOMP._IEnvironment _1320___v60;
        RAST._IExpr _out104;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out105;
        DCOMP._IEnvironment _out106;
        (this).GenStmts((m).dtor_body, _1287_selfIdentifier, _1305_env, true, _1307_earlyReturn, out _out104, out _out105, out _out106);
        _1318_body = _out104;
        _1319___v59 = _out105;
        _1320___v60 = _out106;
        _1304_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1306_preBody).Then(_1318_body));
      } else {
        _1305_env = DCOMP.Environment.create(_1280_paramNames, _1281_paramTypes);
        _1304_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1294_visibility, RAST.Fn.create(_1286_fnName, _1298_typeParams, _1279_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1291_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1291_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1291_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1304_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1321_declarations;
      _1321_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1322_i;
      _1322_i = BigInteger.Zero;
      newEnv = env;
      while ((_1322_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _1323_stmt;
        _1323_stmt = (stmts).Select(_1322_i);
        RAST._IExpr _1324_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1325_recIdents;
        DCOMP._IEnvironment _1326_newEnv2;
        RAST._IExpr _out107;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out108;
        DCOMP._IEnvironment _out109;
        (this).GenStmt(_1323_stmt, selfIdent, newEnv, (isLast) && ((_1322_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out107, out _out108, out _out109);
        _1324_stmtExpr = _out107;
        _1325_recIdents = _out108;
        _1326_newEnv2 = _out109;
        newEnv = _1326_newEnv2;
        DAST._IStatement _source58 = _1323_stmt;
        bool unmatched58 = true;
        if (unmatched58) {
          if (_source58.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1327_name = _source58.dtor_name;
            DAST._IType _1328___v61 = _source58.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> _1329___v62 = _source58.dtor_maybeValue;
            unmatched58 = false;
            {
              _1321_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1321_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_1327_name)));
            }
          }
        }
        if (unmatched58) {
          DAST._IStatement _1330___v63 = _source58;
          unmatched58 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1325_recIdents, _1321_declarations));
        generated = (generated).Then(_1324_stmtExpr);
        _1322_i = (_1322_i) + (BigInteger.One);
      }
    }
    public void GenAssignLhs(DAST._IAssignLhs lhs, RAST._IExpr rhs, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, out RAST._IExpr generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      newEnv = env;
      DAST._IAssignLhs _source59 = lhs;
      bool unmatched59 = true;
      if (unmatched59) {
        if (_source59.is_Ident) {
          Dafny.ISequence<Dafny.Rune> ident0 = _source59.dtor_ident;
          Dafny.ISequence<Dafny.Rune> _1331_id = ident0;
          unmatched59 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1332_idRust;
            _1332_idRust = DCOMP.__default.escapeName(_1331_id);
            if (((env).IsBorrowed(_1332_idRust)) || ((env).IsBorrowedMut(_1332_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1332_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1332_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1332_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched59) {
        if (_source59.is_Select) {
          DAST._IExpression _1333_on = _source59.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1334_field = _source59.dtor_field;
          unmatched59 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1335_fieldName;
            _1335_fieldName = DCOMP.__default.escapeName(_1334_field);
            RAST._IExpr _1336_onExpr;
            DCOMP._IOwnership _1337_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1338_recIdents;
            RAST._IExpr _out110;
            DCOMP._IOwnership _out111;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out112;
            (this).GenExpr(_1333_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out110, out _out111, out _out112);
            _1336_onExpr = _out110;
            _1337_onOwned = _out111;
            _1338_recIdents = _out112;
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*("), (_1336_onExpr)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _1335_fieldName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()) = ")), (rhs)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";")));
            readIdents = _1338_recIdents;
            needsIIFE = true;
          }
        }
      }
      if (unmatched59) {
        DAST._IExpression _1339_on = _source59.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1340_indices = _source59.dtor_indices;
        unmatched59 = false;
        {
          RAST._IExpr _1341_onExpr;
          DCOMP._IOwnership _1342_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1343_recIdents;
          RAST._IExpr _out113;
          DCOMP._IOwnership _out114;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out115;
          (this).GenExpr(_1339_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out113, out _out114, out _out115);
          _1341_onExpr = _out113;
          _1342_onOwned = _out114;
          _1343_recIdents = _out115;
          readIdents = _1343_recIdents;
          Dafny.ISequence<Dafny.Rune> _1344_r;
          _1344_r = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          BigInteger _1345_i;
          _1345_i = BigInteger.Zero;
          while ((_1345_i) < (new BigInteger((_1340_indices).Count))) {
            RAST._IExpr _1346_idx;
            DCOMP._IOwnership _1347___v64;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1348_recIdentsIdx;
            RAST._IExpr _out116;
            DCOMP._IOwnership _out117;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out118;
            (this).GenExpr((_1340_indices).Select(_1345_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out116, out _out117, out _out118);
            _1346_idx = _out116;
            _1347___v64 = _out117;
            _1348_recIdentsIdx = _out118;
            _1344_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1344_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let __idx")), Std.Strings.__default.OfNat(_1345_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = <usize as ::dafny_runtime::NumCast>::from(")), (_1346_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap();\n"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1348_recIdentsIdx);
            _1345_i = (_1345_i) + (BigInteger.One);
          }
          _1344_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1344_r, (_1341_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()"));
          _1345_i = BigInteger.Zero;
          while ((_1345_i) < (new BigInteger((_1340_indices).Count))) {
            _1344_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1344_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[__idx")), Std.Strings.__default.OfNat(_1345_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
            _1345_i = (_1345_i) + (BigInteger.One);
          }
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1344_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), (rhs)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n}")));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source60 = stmt;
      bool unmatched60 = true;
      if (unmatched60) {
        if (_source60.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1349_name = _source60.dtor_name;
          DAST._IType _1350_typ = _source60.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source60.dtor_maybeValue;
          if (maybeValue0.is_Some) {
            DAST._IExpression _1351_expression = maybeValue0.dtor_value;
            unmatched60 = false;
            {
              RAST._IType _1352_tpe;
              RAST._IType _out119;
              _out119 = (this).GenType(_1350_typ, true, false);
              _1352_tpe = _out119;
              Dafny.ISequence<Dafny.Rune> _1353_varName;
              _1353_varName = DCOMP.__default.escapeName(_1349_name);
              bool _1354_hasCopySemantics;
              _1354_hasCopySemantics = (_1352_tpe).CanReadWithoutClone();
              if (((_1351_expression).is_InitializationValue) && (!(_1354_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1353_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).ApplyType1(_1352_tpe)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1353_varName, RAST.__default.MaybePlaceboType(_1352_tpe));
              } else {
                RAST._IExpr _1355_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1356_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                DCOMP._IOwnership _1357_exprOwnership = DCOMP.Ownership.Default();
                RAST._IExpr _out120;
                DCOMP._IOwnership _out121;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out122;
                (this).GenExpr(_1351_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out120, out _out121, out _out122);
                _1355_expr = _out120;
                _1357_exprOwnership = _out121;
                _1356_recIdents = _out122;
                readIdents = _1356_recIdents;
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_1349_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1352_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1355_expr));
                newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_1349_name), _1352_tpe);
              }
            }
          }
        }
      }
      if (unmatched60) {
        if (_source60.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1358_name = _source60.dtor_name;
          DAST._IType _1359_typ = _source60.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source60.dtor_maybeValue;
          if (maybeValue1.is_None) {
            unmatched60 = false;
            {
              DAST._IStatement _1360_newStmt;
              _1360_newStmt = DAST.Statement.create_DeclareVar(_1358_name, _1359_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1359_typ)));
              RAST._IExpr _out123;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out124;
              DCOMP._IEnvironment _out125;
              (this).GenStmt(_1360_newStmt, selfIdent, env, isLast, earlyReturn, out _out123, out _out124, out _out125);
              generated = _out123;
              readIdents = _out124;
              newEnv = _out125;
            }
          }
        }
      }
      if (unmatched60) {
        if (_source60.is_Assign) {
          DAST._IAssignLhs _1361_lhs = _source60.dtor_lhs;
          DAST._IExpression _1362_expression = _source60.dtor_value;
          unmatched60 = false;
          {
            RAST._IExpr _1363_exprGen;
            DCOMP._IOwnership _1364___v65;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1365_exprIdents;
            RAST._IExpr _out126;
            DCOMP._IOwnership _out127;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out128;
            (this).GenExpr(_1362_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out126, out _out127, out _out128);
            _1363_exprGen = _out126;
            _1364___v65 = _out127;
            _1365_exprIdents = _out128;
            if ((_1361_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1366_rustId;
              _1366_rustId = DCOMP.__default.escapeName(((_1361_lhs).dtor_ident));
              Std.Wrappers._IOption<RAST._IType> _1367_tpe;
              _1367_tpe = (env).GetType(_1366_rustId);
              if (((_1367_tpe).is_Some) && ((((_1367_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1363_exprGen = RAST.__default.MaybePlacebo(_1363_exprGen);
              }
            }
            RAST._IExpr _1368_lhsGen;
            bool _1369_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1370_recIdents;
            DCOMP._IEnvironment _1371_resEnv;
            RAST._IExpr _out129;
            bool _out130;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
            DCOMP._IEnvironment _out132;
            (this).GenAssignLhs(_1361_lhs, _1363_exprGen, selfIdent, env, out _out129, out _out130, out _out131, out _out132);
            _1368_lhsGen = _out129;
            _1369_needsIIFE = _out130;
            _1370_recIdents = _out131;
            _1371_resEnv = _out132;
            generated = _1368_lhsGen;
            newEnv = _1371_resEnv;
            if (_1369_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1370_recIdents, _1365_exprIdents);
          }
        }
      }
      if (unmatched60) {
        if (_source60.is_If) {
          DAST._IExpression _1372_cond = _source60.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1373_thnDafny = _source60.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1374_elsDafny = _source60.dtor_els;
          unmatched60 = false;
          {
            RAST._IExpr _1375_cond;
            DCOMP._IOwnership _1376___v66;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1377_recIdents;
            RAST._IExpr _out133;
            DCOMP._IOwnership _out134;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
            (this).GenExpr(_1372_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out133, out _out134, out _out135);
            _1375_cond = _out133;
            _1376___v66 = _out134;
            _1377_recIdents = _out135;
            Dafny.ISequence<Dafny.Rune> _1378_condString;
            _1378_condString = (_1375_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1377_recIdents;
            RAST._IExpr _1379_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1380_thnIdents;
            DCOMP._IEnvironment _1381_thnEnv;
            RAST._IExpr _out136;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
            DCOMP._IEnvironment _out138;
            (this).GenStmts(_1373_thnDafny, selfIdent, env, isLast, earlyReturn, out _out136, out _out137, out _out138);
            _1379_thn = _out136;
            _1380_thnIdents = _out137;
            _1381_thnEnv = _out138;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1380_thnIdents);
            RAST._IExpr _1382_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1383_elsIdents;
            DCOMP._IEnvironment _1384_elsEnv;
            RAST._IExpr _out139;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out140;
            DCOMP._IEnvironment _out141;
            (this).GenStmts(_1374_elsDafny, selfIdent, env, isLast, earlyReturn, out _out139, out _out140, out _out141);
            _1382_els = _out139;
            _1383_elsIdents = _out140;
            _1384_elsEnv = _out141;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1383_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1375_cond, _1379_thn, _1382_els);
          }
        }
      }
      if (unmatched60) {
        if (_source60.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1385_lbl = _source60.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1386_body = _source60.dtor_body;
          unmatched60 = false;
          {
            RAST._IExpr _1387_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1388_bodyIdents;
            DCOMP._IEnvironment _1389_env2;
            RAST._IExpr _out142;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out143;
            DCOMP._IEnvironment _out144;
            (this).GenStmts(_1386_body, selfIdent, env, isLast, earlyReturn, out _out142, out _out143, out _out144);
            _1387_body = _out142;
            _1388_bodyIdents = _out143;
            _1389_env2 = _out144;
            readIdents = _1388_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1385_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1387_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched60) {
        if (_source60.is_While) {
          DAST._IExpression _1390_cond = _source60.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1391_body = _source60.dtor_body;
          unmatched60 = false;
          {
            RAST._IExpr _1392_cond;
            DCOMP._IOwnership _1393___v67;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1394_recIdents;
            RAST._IExpr _out145;
            DCOMP._IOwnership _out146;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out147;
            (this).GenExpr(_1390_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out145, out _out146, out _out147);
            _1392_cond = _out145;
            _1393___v67 = _out146;
            _1394_recIdents = _out147;
            readIdents = _1394_recIdents;
            RAST._IExpr _1395_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1396_bodyIdents;
            DCOMP._IEnvironment _1397_bodyEnv;
            RAST._IExpr _out148;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out149;
            DCOMP._IEnvironment _out150;
            (this).GenStmts(_1391_body, selfIdent, env, false, earlyReturn, out _out148, out _out149, out _out150);
            _1395_bodyExpr = _out148;
            _1396_bodyIdents = _out149;
            _1397_bodyEnv = _out150;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1396_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1392_cond), _1395_bodyExpr);
          }
        }
      }
      if (unmatched60) {
        if (_source60.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1398_boundName = _source60.dtor_boundName;
          DAST._IType _1399_boundType = _source60.dtor_boundType;
          DAST._IExpression _1400_over = _source60.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1401_body = _source60.dtor_body;
          unmatched60 = false;
          {
            RAST._IExpr _1402_over;
            DCOMP._IOwnership _1403___v68;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1404_recIdents;
            RAST._IExpr _out151;
            DCOMP._IOwnership _out152;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out153;
            (this).GenExpr(_1400_over, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out151, out _out152, out _out153);
            _1402_over = _out151;
            _1403___v68 = _out152;
            _1404_recIdents = _out153;
            RAST._IType _1405_boundTpe;
            RAST._IType _out154;
            _out154 = (this).GenType(_1399_boundType, false, false);
            _1405_boundTpe = _out154;
            readIdents = _1404_recIdents;
            Dafny.ISequence<Dafny.Rune> _1406_boundRName;
            _1406_boundRName = DCOMP.__default.escapeName(_1398_boundName);
            RAST._IExpr _1407_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1408_bodyIdents;
            DCOMP._IEnvironment _1409_bodyEnv;
            RAST._IExpr _out155;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
            DCOMP._IEnvironment _out157;
            (this).GenStmts(_1401_body, selfIdent, (env).AddAssigned(_1406_boundRName, _1405_boundTpe), false, earlyReturn, out _out155, out _out156, out _out157);
            _1407_bodyExpr = _out155;
            _1408_bodyIdents = _out156;
            _1409_bodyEnv = _out157;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1408_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1406_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1406_boundRName, _1402_over, _1407_bodyExpr);
          }
        }
      }
      if (unmatched60) {
        if (_source60.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1410_toLabel = _source60.dtor_toLabel;
          unmatched60 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source61 = _1410_toLabel;
            bool unmatched61 = true;
            if (unmatched61) {
              if (_source61.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1411_lbl = _source61.dtor_value;
                unmatched61 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1411_lbl)));
                }
              }
            }
            if (unmatched61) {
              unmatched61 = false;
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched60) {
        if (_source60.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1412_body = _source60.dtor_body;
          unmatched60 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
            }
            newEnv = env;
            BigInteger _hi27 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1413_paramI = BigInteger.Zero; _1413_paramI < _hi27; _1413_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1414_param;
              _1414_param = ((env).dtor_names).Select(_1413_paramI);
              RAST._IExpr _1415_paramInit;
              DCOMP._IOwnership _1416___v69;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1417___v70;
              RAST._IExpr _out158;
              DCOMP._IOwnership _out159;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out160;
              (this).GenIdent(_1414_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out158, out _out159, out _out160);
              _1415_paramInit = _out158;
              _1416___v69 = _out159;
              _1417___v70 = _out160;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1414_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1415_paramInit)));
              if (((env).dtor_types).Contains(_1414_param)) {
                RAST._IType _1418_declaredType;
                _1418_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1414_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1414_param, _1418_declaredType);
              }
            }
            RAST._IExpr _1419_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1420_bodyIdents;
            DCOMP._IEnvironment _1421_bodyEnv;
            RAST._IExpr _out161;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out162;
            DCOMP._IEnvironment _out163;
            (this).GenStmts(_1412_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), newEnv, false, earlyReturn, out _out161, out _out162, out _out163);
            _1419_bodyExpr = _out161;
            _1420_bodyIdents = _out162;
            _1421_bodyEnv = _out163;
            readIdents = _1420_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1419_bodyExpr)));
          }
        }
      }
      if (unmatched60) {
        if (_source60.is_JumpTailCallStart) {
          unmatched60 = false;
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched60) {
        if (_source60.is_Call) {
          DAST._IExpression _1422_on = _source60.dtor_on;
          DAST._ICallName _1423_name = _source60.dtor_callName;
          Dafny.ISequence<DAST._IType> _1424_typeArgs = _source60.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1425_args = _source60.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1426_maybeOutVars = _source60.dtor_outs;
          unmatched60 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IExpr _1427_onExpr;
            DCOMP._IOwnership _1428___v71;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1429_enclosingIdents;
            RAST._IExpr _out164;
            DCOMP._IOwnership _out165;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out166;
            (this).GenExpr(_1422_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out164, out _out165, out _out166);
            _1427_onExpr = _out164;
            _1428___v71 = _out165;
            _1429_enclosingIdents = _out166;
            Dafny.ISequence<RAST._IType> _1430_typeArgsR;
            _1430_typeArgsR = Dafny.Sequence<RAST._IType>.FromElements();
            if ((new BigInteger((_1424_typeArgs).Count)) >= (BigInteger.One)) {
              BigInteger _1431_typeI;
              _1431_typeI = BigInteger.Zero;
              while ((_1431_typeI) < (new BigInteger((_1424_typeArgs).Count))) {
                RAST._IType _1432_tpe;
                RAST._IType _out167;
                _out167 = (this).GenType((_1424_typeArgs).Select(_1431_typeI), false, false);
                _1432_tpe = _out167;
                _1430_typeArgsR = Dafny.Sequence<RAST._IType>.Concat(_1430_typeArgsR, Dafny.Sequence<RAST._IType>.FromElements(_1432_tpe));
                _1431_typeI = (_1431_typeI) + (BigInteger.One);
              }
            }
            Dafny.ISequence<RAST._IExpr> _1433_argExprs;
            _1433_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi28 = new BigInteger((_1425_args).Count);
            for (BigInteger _1434_i = BigInteger.Zero; _1434_i < _hi28; _1434_i++) {
              DCOMP._IOwnership _1435_argOwnership;
              _1435_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              if (((_1423_name).is_CallName) && ((_1434_i) < (new BigInteger((((_1423_name).dtor_signature)).Count)))) {
                RAST._IType _1436_tpe;
                RAST._IType _out168;
                _out168 = (this).GenType(((((_1423_name).dtor_signature)).Select(_1434_i)).dtor_typ, false, false);
                _1436_tpe = _out168;
                if ((_1436_tpe).CanReadWithoutClone()) {
                  _1435_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
                }
              }
              RAST._IExpr _1437_argExpr;
              DCOMP._IOwnership _1438_ownership;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1439_argIdents;
              RAST._IExpr _out169;
              DCOMP._IOwnership _out170;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out171;
              (this).GenExpr((_1425_args).Select(_1434_i), selfIdent, env, _1435_argOwnership, out _out169, out _out170, out _out171);
              _1437_argExpr = _out169;
              _1438_ownership = _out170;
              _1439_argIdents = _out171;
              _1433_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1433_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1437_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1439_argIdents);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1429_enclosingIdents);
            Dafny.ISequence<Dafny.Rune> _1440_renderedName;
            _1440_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
              DAST._ICallName _source62 = _1423_name;
              bool unmatched62 = true;
              if (unmatched62) {
                if (_source62.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _1441_name = _source62.dtor_name;
                  Std.Wrappers._IOption<DAST._IType> _1442___v72 = _source62.dtor_onType;
                  Dafny.ISequence<DAST._IFormal> _1443___v73 = _source62.dtor_signature;
                  unmatched62 = false;
                  return DCOMP.__default.escapeName(_1441_name);
                }
              }
              if (unmatched62) {
                bool disjunctiveMatch9 = false;
                if (_source62.is_MapBuilderAdd) {
                  disjunctiveMatch9 = true;
                }
                if (_source62.is_SetBuilderAdd) {
                  disjunctiveMatch9 = true;
                }
                if (disjunctiveMatch9) {
                  unmatched62 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                }
              }
              if (unmatched62) {
                bool disjunctiveMatch10 = false;
                disjunctiveMatch10 = true;
                disjunctiveMatch10 = true;
                if (disjunctiveMatch10) {
                  unmatched62 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                }
              }
              throw new System.Exception("unexpected control point");
            }))();
            DAST._IExpression _source63 = _1422_on;
            bool unmatched63 = true;
            if (unmatched63) {
              if (_source63.is_Companion) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1444___v74 = _source63.dtor_Companion_a0;
                unmatched63 = false;
                {
                  _1427_onExpr = (_1427_onExpr).MSel(_1440_renderedName);
                }
              }
            }
            if (unmatched63) {
              DAST._IExpression _1445___v75 = _source63;
              unmatched63 = false;
              {
                _1427_onExpr = (_1427_onExpr).Sel(_1440_renderedName);
              }
            }
            generated = _1427_onExpr;
            if ((new BigInteger((_1430_typeArgsR).Count)).Sign == 1) {
              generated = (generated).ApplyType(_1430_typeArgsR);
            }
            generated = (generated).Apply(_1433_argExprs);
            if (((_1426_maybeOutVars).is_Some) && ((new BigInteger(((_1426_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1446_outVar;
              _1446_outVar = DCOMP.__default.escapeName((((_1426_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
              if (!((env).CanReadWithoutClone(_1446_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1446_outVar, generated);
            } else if (((_1426_maybeOutVars).is_None) || ((new BigInteger(((_1426_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1447_tmpVar;
              _1447_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1448_tmpId;
              _1448_tmpId = RAST.Expr.create_Identifier(_1447_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1447_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1449_outVars;
              _1449_outVars = (_1426_maybeOutVars).dtor_value;
              BigInteger _hi29 = new BigInteger((_1449_outVars).Count);
              for (BigInteger _1450_outI = BigInteger.Zero; _1450_outI < _hi29; _1450_outI++) {
                Dafny.ISequence<Dafny.Rune> _1451_outVar;
                _1451_outVar = DCOMP.__default.escapeName(((_1449_outVars).Select(_1450_outI)));
                RAST._IExpr _1452_rhs;
                _1452_rhs = (_1448_tmpId).Sel(Std.Strings.__default.OfNat(_1450_outI));
                if (!((env).CanReadWithoutClone(_1451_outVar))) {
                  _1452_rhs = RAST.__default.MaybePlacebo(_1452_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1451_outVar, _1452_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched60) {
        if (_source60.is_Return) {
          DAST._IExpression _1453_exprDafny = _source60.dtor_expr;
          unmatched60 = false;
          {
            RAST._IExpr _1454_expr;
            DCOMP._IOwnership _1455___v76;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1456_recIdents;
            RAST._IExpr _out172;
            DCOMP._IOwnership _out173;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out174;
            (this).GenExpr(_1453_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out172, out _out173, out _out174);
            _1454_expr = _out172;
            _1455___v76 = _out173;
            _1456_recIdents = _out174;
            readIdents = _1456_recIdents;
            if (isLast) {
              generated = _1454_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1454_expr));
            }
            newEnv = env;
          }
        }
      }
      if (unmatched60) {
        if (_source60.is_EarlyReturn) {
          unmatched60 = false;
          {
            generated = earlyReturn;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched60) {
        if (_source60.is_Halt) {
          unmatched60 = false;
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched60) {
        DAST._IExpression _1457_e = _source60.dtor_Print_a0;
        unmatched60 = false;
        {
          RAST._IExpr _1458_printedExpr;
          DCOMP._IOwnership _1459_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1460_recIdents;
          RAST._IExpr _out175;
          DCOMP._IOwnership _out176;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
          (this).GenExpr(_1457_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out175, out _out176, out _out177);
          _1458_printedExpr = _out175;
          _1459_recOwnership = _out176;
          _1460_recIdents = _out177;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1458_printedExpr)));
          readIdents = _1460_recIdents;
          newEnv = env;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source64 = range;
      bool unmatched64 = true;
      if (unmatched64) {
        if (_source64.is_NoRange) {
          unmatched64 = false;
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      if (unmatched64) {
        if (_source64.is_U8) {
          unmatched64 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      if (unmatched64) {
        if (_source64.is_U16) {
          unmatched64 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      if (unmatched64) {
        if (_source64.is_U32) {
          unmatched64 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      if (unmatched64) {
        if (_source64.is_U64) {
          unmatched64 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      if (unmatched64) {
        if (_source64.is_U128) {
          unmatched64 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      if (unmatched64) {
        if (_source64.is_I8) {
          unmatched64 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      if (unmatched64) {
        if (_source64.is_I16) {
          unmatched64 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      if (unmatched64) {
        if (_source64.is_I32) {
          unmatched64 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      if (unmatched64) {
        if (_source64.is_I64) {
          unmatched64 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      if (unmatched64) {
        if (_source64.is_I128) {
          unmatched64 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
        }
      }
      if (unmatched64) {
        DAST._INewtypeRange _1461___v77 = _source64;
        unmatched64 = false;
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
        RAST._IExpr _out178;
        DCOMP._IOwnership _out179;
        DCOMP.COMP.FromOwned(r, expectedOwnership, out _out178, out _out179);
        @out = _out178;
        resultingOwnership = _out179;
        return ;
      } else if (object.Equals(ownership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        RAST._IExpr _out180;
        DCOMP._IOwnership _out181;
        DCOMP.COMP.FromOwned(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), r, DAST.Format.UnaryOpFormat.create_NoFormat()), expectedOwnership, out _out180, out _out181);
        @out = _out180;
        resultingOwnership = _out181;
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
      DAST._IExpression _source65 = e;
      bool unmatched65 = true;
      if (unmatched65) {
        if (_source65.is_Literal) {
          DAST._ILiteral _h150 = _source65.dtor_Literal_a0;
          if (_h150.is_BoolLiteral) {
            bool _1462_b = _h150.dtor_BoolLiteral_a0;
            unmatched65 = false;
            {
              RAST._IExpr _out182;
              DCOMP._IOwnership _out183;
              DCOMP.COMP.FromOwned(RAST.Expr.create_LiteralBool(_1462_b), expectedOwnership, out _out182, out _out183);
              r = _out182;
              resultingOwnership = _out183;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_Literal) {
          DAST._ILiteral _h151 = _source65.dtor_Literal_a0;
          if (_h151.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1463_i = _h151.dtor_IntLiteral_a0;
            DAST._IType _1464_t = _h151.dtor_IntLiteral_a1;
            unmatched65 = false;
            {
              DAST._IType _source66 = _1464_t;
              bool unmatched66 = true;
              if (unmatched66) {
                if (_source66.is_Primitive) {
                  DAST._IPrimitive _h90 = _source66.dtor_Primitive_a0;
                  if (_h90.is_Int) {
                    unmatched66 = false;
                    {
                      if ((new BigInteger((_1463_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1463_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1463_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched66) {
                DAST._IType _1465_o = _source66;
                unmatched66 = false;
                {
                  RAST._IType _1466_genType;
                  RAST._IType _out184;
                  _out184 = (this).GenType(_1465_o, false, false);
                  _1466_genType = _out184;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1463_i), _1466_genType);
                }
              }
              RAST._IExpr _out185;
              DCOMP._IOwnership _out186;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out185, out _out186);
              r = _out185;
              resultingOwnership = _out186;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_Literal) {
          DAST._ILiteral _h152 = _source65.dtor_Literal_a0;
          if (_h152.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1467_n = _h152.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1468_d = _h152.dtor_DecLiteral_a1;
            DAST._IType _1469_t = _h152.dtor_DecLiteral_a2;
            unmatched65 = false;
            {
              DAST._IType _source67 = _1469_t;
              bool unmatched67 = true;
              if (unmatched67) {
                if (_source67.is_Primitive) {
                  DAST._IPrimitive _h91 = _source67.dtor_Primitive_a0;
                  if (_h91.is_Real) {
                    unmatched67 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1467_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1468_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched67) {
                DAST._IType _1470_o = _source67;
                unmatched67 = false;
                {
                  RAST._IType _1471_genType;
                  RAST._IType _out187;
                  _out187 = (this).GenType(_1470_o, false, false);
                  _1471_genType = _out187;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1467_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1468_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1471_genType);
                }
              }
              RAST._IExpr _out188;
              DCOMP._IOwnership _out189;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out188, out _out189);
              r = _out188;
              resultingOwnership = _out189;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_Literal) {
          DAST._ILiteral _h153 = _source65.dtor_Literal_a0;
          if (_h153.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1472_l = _h153.dtor_StringLiteral_a0;
            bool _1473_verbatim = _h153.dtor_verbatim;
            unmatched65 = false;
            {
              if (_1473_verbatim) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Verbatim strings prefixed by @ not supported yet."));
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1472_l, false, _1473_verbatim));
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
      if (unmatched65) {
        if (_source65.is_Literal) {
          DAST._ILiteral _h154 = _source65.dtor_Literal_a0;
          if (_h154.is_CharLiteralUTF16) {
            BigInteger _1474_c = _h154.dtor_CharLiteralUTF16_a0;
            unmatched65 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1474_c));
              r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
              RAST._IExpr _out192;
              DCOMP._IOwnership _out193;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out192, out _out193);
              r = _out192;
              resultingOwnership = _out193;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_Literal) {
          DAST._ILiteral _h155 = _source65.dtor_Literal_a0;
          if (_h155.is_CharLiteral) {
            Dafny.Rune _1475_c = _h155.dtor_CharLiteral_a0;
            unmatched65 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1475_c).Value)));
              if (!((this).UnicodeChars)) {
                r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              } else {
                r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
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
      if (unmatched65) {
        DAST._ILiteral _h156 = _source65.dtor_Literal_a0;
        DAST._IType _1476_tpe = _h156.dtor_Null_a0;
        unmatched65 = false;
        {
          RAST._IType _1477_tpeGen;
          RAST._IType _out196;
          _out196 = (this).GenType(_1476_tpe, false, false);
          _1477_tpeGen = _out196;
          r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None")), _1477_tpeGen);
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
    public void GenExprBinary(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs52 = e;
      DAST._IBinOp _1478_op = _let_tmp_rhs52.dtor_op;
      DAST._IExpression _1479_lExpr = _let_tmp_rhs52.dtor_left;
      DAST._IExpression _1480_rExpr = _let_tmp_rhs52.dtor_right;
      DAST.Format._IBinaryOpFormat _1481_format = _let_tmp_rhs52.dtor_format2;
      bool _1482_becomesLeftCallsRight;
      _1482_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source68 = _1478_op;
        bool unmatched68 = true;
        if (unmatched68) {
          bool disjunctiveMatch11 = false;
          if (_source68.is_SetMerge) {
            disjunctiveMatch11 = true;
          }
          if (_source68.is_SetSubtraction) {
            disjunctiveMatch11 = true;
          }
          if (_source68.is_SetIntersection) {
            disjunctiveMatch11 = true;
          }
          if (_source68.is_SetDisjoint) {
            disjunctiveMatch11 = true;
          }
          if (_source68.is_MapMerge) {
            disjunctiveMatch11 = true;
          }
          if (_source68.is_MapSubtraction) {
            disjunctiveMatch11 = true;
          }
          if (_source68.is_MultisetMerge) {
            disjunctiveMatch11 = true;
          }
          if (_source68.is_MultisetSubtraction) {
            disjunctiveMatch11 = true;
          }
          if (_source68.is_MultisetIntersection) {
            disjunctiveMatch11 = true;
          }
          if (_source68.is_MultisetDisjoint) {
            disjunctiveMatch11 = true;
          }
          if (_source68.is_Concat) {
            disjunctiveMatch11 = true;
          }
          if (disjunctiveMatch11) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          DAST._IBinOp _1483___v78 = _source68;
          unmatched68 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1484_becomesRightCallsLeft;
      _1484_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source69 = _1478_op;
        bool unmatched69 = true;
        if (unmatched69) {
          if (_source69.is_In) {
            unmatched69 = false;
            return true;
          }
        }
        if (unmatched69) {
          DAST._IBinOp _1485___v79 = _source69;
          unmatched69 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1486_becomesCallLeftRight;
      _1486_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source70 = _1478_op;
        bool unmatched70 = true;
        if (unmatched70) {
          if (_source70.is_Eq) {
            bool referential0 = _source70.dtor_referential;
            if ((referential0) == (true)) {
              bool nullable0 = _source70.dtor_nullable;
              if ((nullable0) == (false)) {
                unmatched70 = false;
                return true;
              }
            }
          }
        }
        if (unmatched70) {
          if (_source70.is_SetMerge) {
            unmatched70 = false;
            return true;
          }
        }
        if (unmatched70) {
          if (_source70.is_SetSubtraction) {
            unmatched70 = false;
            return true;
          }
        }
        if (unmatched70) {
          if (_source70.is_SetIntersection) {
            unmatched70 = false;
            return true;
          }
        }
        if (unmatched70) {
          if (_source70.is_SetDisjoint) {
            unmatched70 = false;
            return true;
          }
        }
        if (unmatched70) {
          if (_source70.is_MapMerge) {
            unmatched70 = false;
            return true;
          }
        }
        if (unmatched70) {
          if (_source70.is_MapSubtraction) {
            unmatched70 = false;
            return true;
          }
        }
        if (unmatched70) {
          if (_source70.is_MultisetMerge) {
            unmatched70 = false;
            return true;
          }
        }
        if (unmatched70) {
          if (_source70.is_MultisetSubtraction) {
            unmatched70 = false;
            return true;
          }
        }
        if (unmatched70) {
          if (_source70.is_MultisetIntersection) {
            unmatched70 = false;
            return true;
          }
        }
        if (unmatched70) {
          if (_source70.is_MultisetDisjoint) {
            unmatched70 = false;
            return true;
          }
        }
        if (unmatched70) {
          if (_source70.is_Concat) {
            unmatched70 = false;
            return true;
          }
        }
        if (unmatched70) {
          DAST._IBinOp _1487___v80 = _source70;
          unmatched70 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      DCOMP._IOwnership _1488_expectedLeftOwnership;
      _1488_expectedLeftOwnership = ((_1482_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1484_becomesRightCallsLeft) || (_1486_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1489_expectedRightOwnership;
      _1489_expectedRightOwnership = (((_1482_becomesLeftCallsRight) || (_1486_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1484_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1490_left;
      DCOMP._IOwnership _1491___v81;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1492_recIdentsL;
      RAST._IExpr _out199;
      DCOMP._IOwnership _out200;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out201;
      (this).GenExpr(_1479_lExpr, selfIdent, env, _1488_expectedLeftOwnership, out _out199, out _out200, out _out201);
      _1490_left = _out199;
      _1491___v81 = _out200;
      _1492_recIdentsL = _out201;
      RAST._IExpr _1493_right;
      DCOMP._IOwnership _1494___v82;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1495_recIdentsR;
      RAST._IExpr _out202;
      DCOMP._IOwnership _out203;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out204;
      (this).GenExpr(_1480_rExpr, selfIdent, env, _1489_expectedRightOwnership, out _out202, out _out203, out _out204);
      _1493_right = _out202;
      _1494___v82 = _out203;
      _1495_recIdentsR = _out204;
      DAST._IBinOp _source71 = _1478_op;
      bool unmatched71 = true;
      if (unmatched71) {
        if (_source71.is_In) {
          unmatched71 = false;
          {
            r = ((_1493_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1490_left);
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_SeqProperPrefix) {
          unmatched71 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1490_left, _1493_right, _1481_format);
        }
      }
      if (unmatched71) {
        if (_source71.is_SeqPrefix) {
          unmatched71 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1490_left, _1493_right, _1481_format);
        }
      }
      if (unmatched71) {
        if (_source71.is_SetMerge) {
          unmatched71 = false;
          {
            r = ((_1490_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1493_right);
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_SetSubtraction) {
          unmatched71 = false;
          {
            r = ((_1490_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1493_right);
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_SetIntersection) {
          unmatched71 = false;
          {
            r = ((_1490_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1493_right);
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_Subset) {
          unmatched71 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1490_left, _1493_right, _1481_format);
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_ProperSubset) {
          unmatched71 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1490_left, _1493_right, _1481_format);
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_SetDisjoint) {
          unmatched71 = false;
          {
            r = ((_1490_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1493_right);
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_MapMerge) {
          unmatched71 = false;
          {
            r = ((_1490_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1493_right);
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_MapSubtraction) {
          unmatched71 = false;
          {
            r = ((_1490_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1493_right);
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_MultisetMerge) {
          unmatched71 = false;
          {
            r = ((_1490_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1493_right);
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_MultisetSubtraction) {
          unmatched71 = false;
          {
            r = ((_1490_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1493_right);
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_MultisetIntersection) {
          unmatched71 = false;
          {
            r = ((_1490_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1493_right);
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_Submultiset) {
          unmatched71 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1490_left, _1493_right, _1481_format);
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_ProperSubmultiset) {
          unmatched71 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1490_left, _1493_right, _1481_format);
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_MultisetDisjoint) {
          unmatched71 = false;
          {
            r = ((_1490_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1493_right);
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_Concat) {
          unmatched71 = false;
          {
            r = ((_1490_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1493_right);
          }
        }
      }
      if (unmatched71) {
        DAST._IBinOp _1496___v83 = _source71;
        unmatched71 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1478_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1478_op), _1490_left, _1493_right, _1481_format);
          } else {
            DAST._IBinOp _source72 = _1478_op;
            bool unmatched72 = true;
            if (unmatched72) {
              if (_source72.is_Eq) {
                bool _1497_referential = _source72.dtor_referential;
                bool _1498_nullable = _source72.dtor_nullable;
                unmatched72 = false;
                {
                  if (_1497_referential) {
                    if (_1498_nullable) {
                      r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1490_left, _1493_right));
                    } else {
                      r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1490_left, _1493_right));
                    }
                  } else {
                    r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1490_left, _1493_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                  }
                }
              }
            }
            if (unmatched72) {
              if (_source72.is_EuclidianDiv) {
                unmatched72 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1490_left, _1493_right));
                }
              }
            }
            if (unmatched72) {
              if (_source72.is_EuclidianMod) {
                unmatched72 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1490_left, _1493_right));
                }
              }
            }
            if (unmatched72) {
              Dafny.ISequence<Dafny.Rune> _1499_op = _source72.dtor_Passthrough_a0;
              unmatched72 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1499_op, _1490_left, _1493_right, _1481_format);
              }
            }
          }
        }
      }
      RAST._IExpr _out205;
      DCOMP._IOwnership _out206;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out205, out _out206);
      r = _out205;
      resultingOwnership = _out206;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1492_recIdentsL, _1495_recIdentsR);
      return ;
    }
    public void GenExprConvertFromNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs53 = e;
      DAST._IExpression _1500_expr = _let_tmp_rhs53.dtor_value;
      DAST._IType _1501_fromTpe = _let_tmp_rhs53.dtor_from;
      DAST._IType _1502_toTpe = _let_tmp_rhs53.dtor_typ;
      RAST._IExpr _1503_recursiveGen;
      DCOMP._IOwnership _1504_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1505_recIdents;
      RAST._IExpr _out207;
      DCOMP._IOwnership _out208;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out209;
      (this).GenExpr(_1500_expr, selfIdent, env, expectedOwnership, out _out207, out _out208, out _out209);
      _1503_recursiveGen = _out207;
      _1504_recOwned = _out208;
      _1505_recIdents = _out209;
      r = _1503_recursiveGen;
      if (object.Equals(_1504_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      RAST._IExpr _out210;
      DCOMP._IOwnership _out211;
      DCOMP.COMP.FromOwnership(r, _1504_recOwned, expectedOwnership, out _out210, out _out211);
      r = _out210;
      resultingOwnership = _out211;
      readIdents = _1505_recIdents;
    }
    public void GenExprConvertToNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IExpression _1506_expr = _let_tmp_rhs54.dtor_value;
      DAST._IType _1507_fromTpe = _let_tmp_rhs54.dtor_from;
      DAST._IType _1508_toTpe = _let_tmp_rhs54.dtor_typ;
      RAST._IExpr _1509_recursiveGen;
      DCOMP._IOwnership _1510_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1511_recIdents;
      RAST._IExpr _out212;
      DCOMP._IOwnership _out213;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out214;
      (this).GenExpr(_1506_expr, selfIdent, env, expectedOwnership, out _out212, out _out213, out _out214);
      _1509_recursiveGen = _out212;
      _1510_recOwned = _out213;
      _1511_recIdents = _out214;
      r = _1509_recursiveGen;
      if (object.Equals(_1510_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
      RAST._IExpr _out215;
      DCOMP._IOwnership _out216;
      DCOMP.COMP.FromOwnership(r, _1510_recOwned, expectedOwnership, out _out215, out _out216);
      r = _out215;
      resultingOwnership = _out216;
      readIdents = _1511_recIdents;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _1512_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _1513_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _1514_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _1514_toTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1515___v84 = _let_tmp_rhs56.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _1516___v85 = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      DAST._IType _1517_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _1518_range = _let_tmp_rhs57.dtor_range;
      bool _1519_erase = _let_tmp_rhs57.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1520_attributes = _let_tmp_rhs57.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _1521_nativeToType;
      _1521_nativeToType = DCOMP.COMP.NewtypeToRustType(_1517_b, _1518_range);
      if (object.Equals(_1513_fromTpe, _1517_b)) {
        RAST._IExpr _1522_recursiveGen;
        DCOMP._IOwnership _1523_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1524_recIdents;
        RAST._IExpr _out217;
        DCOMP._IOwnership _out218;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out219;
        (this).GenExpr(_1512_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out217, out _out218, out _out219);
        _1522_recursiveGen = _out217;
        _1523_recOwned = _out218;
        _1524_recIdents = _out219;
        readIdents = _1524_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source73 = _1521_nativeToType;
        bool unmatched73 = true;
        if (unmatched73) {
          if (_source73.is_Some) {
            RAST._IType _1525_v = _source73.dtor_value;
            unmatched73 = false;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1522_recursiveGen, RAST.Expr.create_ExprFromType(_1525_v)));
            RAST._IExpr _out220;
            DCOMP._IOwnership _out221;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out220, out _out221);
            r = _out220;
            resultingOwnership = _out221;
          }
        }
        if (unmatched73) {
          unmatched73 = false;
          if (_1519_erase) {
            r = _1522_recursiveGen;
          } else {
            RAST._IType _1526_rhsType;
            RAST._IType _out222;
            _out222 = (this).GenType(_1514_toTpe, true, false);
            _1526_rhsType = _out222;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1526_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1522_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out223;
          DCOMP._IOwnership _out224;
          DCOMP.COMP.FromOwnership(r, _1523_recOwned, expectedOwnership, out _out223, out _out224);
          r = _out223;
          resultingOwnership = _out224;
        }
      } else {
        if ((_1521_nativeToType).is_Some) {
          DAST._IType _source74 = _1513_fromTpe;
          bool unmatched74 = true;
          if (unmatched74) {
            if (_source74.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1527___v86 = _source74.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _1528___v87 = _source74.dtor_typeArgs;
              DAST._IResolvedType resolved1 = _source74.dtor_resolved;
              if (resolved1.is_Newtype) {
                DAST._IType _1529_b0 = resolved1.dtor_baseType;
                DAST._INewtypeRange _1530_range0 = resolved1.dtor_range;
                bool _1531_erase0 = resolved1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1532_attributes0 = resolved1.dtor_attributes;
                unmatched74 = false;
                {
                  Std.Wrappers._IOption<RAST._IType> _1533_nativeFromType;
                  _1533_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1529_b0, _1530_range0);
                  if ((_1533_nativeFromType).is_Some) {
                    RAST._IExpr _1534_recursiveGen;
                    DCOMP._IOwnership _1535_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1536_recIdents;
                    RAST._IExpr _out225;
                    DCOMP._IOwnership _out226;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out227;
                    (this).GenExpr(_1512_expr, selfIdent, env, expectedOwnership, out _out225, out _out226, out _out227);
                    _1534_recursiveGen = _out225;
                    _1535_recOwned = _out226;
                    _1536_recIdents = _out227;
                    RAST._IExpr _out228;
                    DCOMP._IOwnership _out229;
                    DCOMP.COMP.FromOwnership(RAST.Expr.create_TypeAscription(_1534_recursiveGen, (_1521_nativeToType).dtor_value), _1535_recOwned, expectedOwnership, out _out228, out _out229);
                    r = _out228;
                    resultingOwnership = _out229;
                    readIdents = _1536_recIdents;
                    return ;
                  }
                }
              }
            }
          }
          if (unmatched74) {
            DAST._IType _1537___v88 = _source74;
            unmatched74 = false;
          }
          if (object.Equals(_1513_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1538_recursiveGen;
            DCOMP._IOwnership _1539_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1540_recIdents;
            RAST._IExpr _out230;
            DCOMP._IOwnership _out231;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out232;
            (this).GenExpr(_1512_expr, selfIdent, env, expectedOwnership, out _out230, out _out231, out _out232);
            _1538_recursiveGen = _out230;
            _1539_recOwned = _out231;
            _1540_recIdents = _out232;
            RAST._IExpr _out233;
            DCOMP._IOwnership _out234;
            DCOMP.COMP.FromOwnership(RAST.Expr.create_TypeAscription((_1538_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1521_nativeToType).dtor_value), _1539_recOwned, expectedOwnership, out _out233, out _out234);
            r = _out233;
            resultingOwnership = _out234;
            readIdents = _1540_recIdents;
            return ;
          }
        }
        RAST._IExpr _out235;
        DCOMP._IOwnership _out236;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out237;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1512_expr, _1513_fromTpe, _1517_b), _1517_b, _1514_toTpe), selfIdent, env, expectedOwnership, out _out235, out _out236, out _out237);
        r = _out235;
        resultingOwnership = _out236;
        readIdents = _out237;
      }
    }
    public void GenExprConvertFromNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs58 = e;
      DAST._IExpression _1541_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _1542_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _1543_toTpe = _let_tmp_rhs58.dtor_typ;
      DAST._IType _let_tmp_rhs59 = _1542_fromTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1544___v89 = _let_tmp_rhs59.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _1545___v90 = _let_tmp_rhs59.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs60 = _let_tmp_rhs59.dtor_resolved;
      DAST._IType _1546_b = _let_tmp_rhs60.dtor_baseType;
      DAST._INewtypeRange _1547_range = _let_tmp_rhs60.dtor_range;
      bool _1548_erase = _let_tmp_rhs60.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1549_attributes = _let_tmp_rhs60.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _1550_nativeFromType;
      _1550_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1546_b, _1547_range);
      if (object.Equals(_1546_b, _1543_toTpe)) {
        RAST._IExpr _1551_recursiveGen;
        DCOMP._IOwnership _1552_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1553_recIdents;
        RAST._IExpr _out238;
        DCOMP._IOwnership _out239;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out240;
        (this).GenExpr(_1541_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out238, out _out239, out _out240);
        _1551_recursiveGen = _out238;
        _1552_recOwned = _out239;
        _1553_recIdents = _out240;
        readIdents = _1553_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source75 = _1550_nativeFromType;
        bool unmatched75 = true;
        if (unmatched75) {
          if (_source75.is_Some) {
            RAST._IType _1554_v = _source75.dtor_value;
            unmatched75 = false;
            RAST._IType _1555_toTpeRust;
            RAST._IType _out241;
            _out241 = (this).GenType(_1543_toTpe, false, false);
            _1555_toTpeRust = _out241;
            r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1555_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1551_recursiveGen));
            RAST._IExpr _out242;
            DCOMP._IOwnership _out243;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out242, out _out243);
            r = _out242;
            resultingOwnership = _out243;
          }
        }
        if (unmatched75) {
          unmatched75 = false;
          if (_1548_erase) {
            r = _1551_recursiveGen;
          } else {
            r = (_1551_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out244;
          DCOMP._IOwnership _out245;
          DCOMP.COMP.FromOwnership(r, _1552_recOwned, expectedOwnership, out _out244, out _out245);
          r = _out244;
          resultingOwnership = _out245;
        }
      } else {
        if ((_1550_nativeFromType).is_Some) {
          if (object.Equals(_1543_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1556_recursiveGen;
            DCOMP._IOwnership _1557_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1558_recIdents;
            RAST._IExpr _out246;
            DCOMP._IOwnership _out247;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out248;
            (this).GenExpr(_1541_expr, selfIdent, env, expectedOwnership, out _out246, out _out247, out _out248);
            _1556_recursiveGen = _out246;
            _1557_recOwned = _out247;
            _1558_recIdents = _out248;
            RAST._IExpr _out249;
            DCOMP._IOwnership _out250;
            DCOMP.COMP.FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1556_recursiveGen, (this).DafnyCharUnderlying)), _1557_recOwned, expectedOwnership, out _out249, out _out250);
            r = _out249;
            resultingOwnership = _out250;
            readIdents = _1558_recIdents;
            return ;
          }
        }
        RAST._IExpr _out251;
        DCOMP._IOwnership _out252;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out253;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1541_expr, _1542_fromTpe, _1546_b), _1546_b, _1543_toTpe), selfIdent, env, expectedOwnership, out _out251, out _out252, out _out253);
        r = _out251;
        resultingOwnership = _out252;
        readIdents = _out253;
      }
    }
    public void GenExprConvertNotImplemented(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs61 = e;
      DAST._IExpression _1559_expr = _let_tmp_rhs61.dtor_value;
      DAST._IType _1560_fromTpe = _let_tmp_rhs61.dtor_from;
      DAST._IType _1561_toTpe = _let_tmp_rhs61.dtor_typ;
      RAST._IType _1562_fromTpeGen;
      RAST._IType _out254;
      _out254 = (this).GenType(_1560_fromTpe, true, false);
      _1562_fromTpeGen = _out254;
      RAST._IType _1563_toTpeGen;
      RAST._IType _out255;
      _out255 = (this).GenType(_1561_toTpe, true, false);
      _1563_toTpeGen = _out255;
      RAST._IExpr _1564_recursiveGen;
      DCOMP._IOwnership _1565_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1566_recIdents;
      RAST._IExpr _out256;
      DCOMP._IOwnership _out257;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out258;
      (this).GenExpr(_1559_expr, selfIdent, env, expectedOwnership, out _out256, out _out257, out _out258);
      _1564_recursiveGen = _out256;
      _1565_recOwned = _out257;
      _1566_recIdents = _out258;
      Dafny.ISequence<Dafny.Rune> _1567_msg;
      _1567_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1562_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1563_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1567_msg);
      r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1564_recursiveGen)._ToString(DCOMP.__default.IND), _1567_msg));
      RAST._IExpr _out259;
      DCOMP._IOwnership _out260;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out259, out _out260);
      r = _out259;
      resultingOwnership = _out260;
      readIdents = _1566_recIdents;
    }
    public void GenExprConvert(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs62 = e;
      DAST._IExpression _1568_expr = _let_tmp_rhs62.dtor_value;
      DAST._IType _1569_fromTpe = _let_tmp_rhs62.dtor_from;
      DAST._IType _1570_toTpe = _let_tmp_rhs62.dtor_typ;
      if (object.Equals(_1569_fromTpe, _1570_toTpe)) {
        RAST._IExpr _1571_recursiveGen;
        DCOMP._IOwnership _1572_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1573_recIdents;
        RAST._IExpr _out261;
        DCOMP._IOwnership _out262;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out263;
        (this).GenExpr(_1568_expr, selfIdent, env, expectedOwnership, out _out261, out _out262, out _out263);
        _1571_recursiveGen = _out261;
        _1572_recOwned = _out262;
        _1573_recIdents = _out263;
        r = _1571_recursiveGen;
        RAST._IExpr _out264;
        DCOMP._IOwnership _out265;
        DCOMP.COMP.FromOwnership(r, _1572_recOwned, expectedOwnership, out _out264, out _out265);
        r = _out264;
        resultingOwnership = _out265;
        readIdents = _1573_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source76 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1569_fromTpe, _1570_toTpe);
        bool unmatched76 = true;
        if (unmatched76) {
          DAST._IType _01 = _source76.dtor__0;
          if (_01.is_Nullable) {
            DAST._IType _1574___v91 = _01.dtor_Nullable_a0;
            DAST._IType _1575___v92 = _source76.dtor__1;
            unmatched76 = false;
            {
              RAST._IExpr _out266;
              DCOMP._IOwnership _out267;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out268;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out266, out _out267, out _out268);
              r = _out266;
              resultingOwnership = _out267;
              readIdents = _out268;
            }
          }
        }
        if (unmatched76) {
          DAST._IType _1576___v93 = _source76.dtor__0;
          DAST._IType _11 = _source76.dtor__1;
          if (_11.is_Nullable) {
            DAST._IType _1577___v94 = _11.dtor_Nullable_a0;
            unmatched76 = false;
            {
              RAST._IExpr _out269;
              DCOMP._IOwnership _out270;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out271;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out269, out _out270, out _out271);
              r = _out269;
              resultingOwnership = _out270;
              readIdents = _out271;
            }
          }
        }
        if (unmatched76) {
          DAST._IType _1578___v95 = _source76.dtor__0;
          DAST._IType _12 = _source76.dtor__1;
          if (_12.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1579___v96 = _12.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1580___v97 = _12.dtor_typeArgs;
            DAST._IResolvedType resolved2 = _12.dtor_resolved;
            if (resolved2.is_Newtype) {
              DAST._IType _1581_b = resolved2.dtor_baseType;
              DAST._INewtypeRange _1582_range = resolved2.dtor_range;
              bool _1583_erase = resolved2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1584_attributes = resolved2.dtor_attributes;
              unmatched76 = false;
              {
                RAST._IExpr _out272;
                DCOMP._IOwnership _out273;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out274;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out272, out _out273, out _out274);
                r = _out272;
                resultingOwnership = _out273;
                readIdents = _out274;
              }
            }
          }
        }
        if (unmatched76) {
          DAST._IType _02 = _source76.dtor__0;
          if (_02.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1585___v98 = _02.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1586___v99 = _02.dtor_typeArgs;
            DAST._IResolvedType resolved3 = _02.dtor_resolved;
            if (resolved3.is_Newtype) {
              DAST._IType _1587_b = resolved3.dtor_baseType;
              DAST._INewtypeRange _1588_range = resolved3.dtor_range;
              bool _1589_erase = resolved3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1590_attributes = resolved3.dtor_attributes;
              DAST._IType _1591___v100 = _source76.dtor__1;
              unmatched76 = false;
              {
                RAST._IExpr _out275;
                DCOMP._IOwnership _out276;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out277;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out275, out _out276, out _out277);
                r = _out275;
                resultingOwnership = _out276;
                readIdents = _out277;
              }
            }
          }
        }
        if (unmatched76) {
          DAST._IType _03 = _source76.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h92 = _03.dtor_Primitive_a0;
            if (_h92.is_Int) {
              DAST._IType _13 = _source76.dtor__1;
              if (_13.is_Primitive) {
                DAST._IPrimitive _h93 = _13.dtor_Primitive_a0;
                if (_h93.is_Real) {
                  unmatched76 = false;
                  {
                    RAST._IExpr _1592_recursiveGen;
                    DCOMP._IOwnership _1593___v101;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1594_recIdents;
                    RAST._IExpr _out278;
                    DCOMP._IOwnership _out279;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out280;
                    (this).GenExpr(_1568_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out278, out _out279, out _out280);
                    _1592_recursiveGen = _out278;
                    _1593___v101 = _out279;
                    _1594_recIdents = _out280;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1592_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out281;
                    DCOMP._IOwnership _out282;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out281, out _out282);
                    r = _out281;
                    resultingOwnership = _out282;
                    readIdents = _1594_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched76) {
          DAST._IType _04 = _source76.dtor__0;
          if (_04.is_Primitive) {
            DAST._IPrimitive _h94 = _04.dtor_Primitive_a0;
            if (_h94.is_Real) {
              DAST._IType _14 = _source76.dtor__1;
              if (_14.is_Primitive) {
                DAST._IPrimitive _h95 = _14.dtor_Primitive_a0;
                if (_h95.is_Int) {
                  unmatched76 = false;
                  {
                    RAST._IExpr _1595_recursiveGen;
                    DCOMP._IOwnership _1596___v102;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1597_recIdents;
                    RAST._IExpr _out283;
                    DCOMP._IOwnership _out284;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out285;
                    (this).GenExpr(_1568_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out283, out _out284, out _out285);
                    _1595_recursiveGen = _out283;
                    _1596___v102 = _out284;
                    _1597_recIdents = _out285;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1595_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out286;
                    DCOMP._IOwnership _out287;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out286, out _out287);
                    r = _out286;
                    resultingOwnership = _out287;
                    readIdents = _1597_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched76) {
          DAST._IType _05 = _source76.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h96 = _05.dtor_Primitive_a0;
            if (_h96.is_Int) {
              DAST._IType _15 = _source76.dtor__1;
              if (_15.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1598___v103 = _15.dtor_Passthrough_a0;
                unmatched76 = false;
                {
                  RAST._IType _1599_rhsType;
                  RAST._IType _out288;
                  _out288 = (this).GenType(_1570_toTpe, true, false);
                  _1599_rhsType = _out288;
                  RAST._IExpr _1600_recursiveGen;
                  DCOMP._IOwnership _1601___v104;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1602_recIdents;
                  RAST._IExpr _out289;
                  DCOMP._IOwnership _out290;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out291;
                  (this).GenExpr(_1568_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out289, out _out290, out _out291);
                  _1600_recursiveGen = _out289;
                  _1601___v104 = _out290;
                  _1602_recIdents = _out291;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1599_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1600_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out292;
                  DCOMP._IOwnership _out293;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out292, out _out293);
                  r = _out292;
                  resultingOwnership = _out293;
                  readIdents = _1602_recIdents;
                }
              }
            }
          }
        }
        if (unmatched76) {
          DAST._IType _06 = _source76.dtor__0;
          if (_06.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1603___v105 = _06.dtor_Passthrough_a0;
            DAST._IType _16 = _source76.dtor__1;
            if (_16.is_Primitive) {
              DAST._IPrimitive _h97 = _16.dtor_Primitive_a0;
              if (_h97.is_Int) {
                unmatched76 = false;
                {
                  RAST._IType _1604_rhsType;
                  RAST._IType _out294;
                  _out294 = (this).GenType(_1569_fromTpe, true, false);
                  _1604_rhsType = _out294;
                  RAST._IExpr _1605_recursiveGen;
                  DCOMP._IOwnership _1606___v106;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1607_recIdents;
                  RAST._IExpr _out295;
                  DCOMP._IOwnership _out296;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out297;
                  (this).GenExpr(_1568_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out295, out _out296, out _out297);
                  _1605_recursiveGen = _out295;
                  _1606___v106 = _out296;
                  _1607_recIdents = _out297;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::dafny_runtime::BigInt::from("), (_1605_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")}")));
                  RAST._IExpr _out298;
                  DCOMP._IOwnership _out299;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out298, out _out299);
                  r = _out298;
                  resultingOwnership = _out299;
                  readIdents = _1607_recIdents;
                }
              }
            }
          }
        }
        if (unmatched76) {
          DAST._IType _07 = _source76.dtor__0;
          if (_07.is_Primitive) {
            DAST._IPrimitive _h98 = _07.dtor_Primitive_a0;
            if (_h98.is_Int) {
              DAST._IType _17 = _source76.dtor__1;
              if (_17.is_Primitive) {
                DAST._IPrimitive _h99 = _17.dtor_Primitive_a0;
                if (_h99.is_Char) {
                  unmatched76 = false;
                  {
                    RAST._IType _1608_rhsType;
                    RAST._IType _out300;
                    _out300 = (this).GenType(_1570_toTpe, true, false);
                    _1608_rhsType = _out300;
                    RAST._IExpr _1609_recursiveGen;
                    DCOMP._IOwnership _1610___v107;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1611_recIdents;
                    RAST._IExpr _out301;
                    DCOMP._IOwnership _out302;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out303;
                    (this).GenExpr(_1568_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out301, out _out302, out _out303);
                    _1609_recursiveGen = _out301;
                    _1610___v107 = _out302;
                    _1611_recIdents = _out303;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), (_1609_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()")));
                    RAST._IExpr _out304;
                    DCOMP._IOwnership _out305;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out304, out _out305);
                    r = _out304;
                    resultingOwnership = _out305;
                    readIdents = _1611_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched76) {
          DAST._IType _08 = _source76.dtor__0;
          if (_08.is_Primitive) {
            DAST._IPrimitive _h910 = _08.dtor_Primitive_a0;
            if (_h910.is_Char) {
              DAST._IType _18 = _source76.dtor__1;
              if (_18.is_Primitive) {
                DAST._IPrimitive _h911 = _18.dtor_Primitive_a0;
                if (_h911.is_Int) {
                  unmatched76 = false;
                  {
                    RAST._IType _1612_rhsType;
                    RAST._IType _out306;
                    _out306 = (this).GenType(_1569_fromTpe, true, false);
                    _1612_rhsType = _out306;
                    RAST._IExpr _1613_recursiveGen;
                    DCOMP._IOwnership _1614___v108;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1615_recIdents;
                    RAST._IExpr _out307;
                    DCOMP._IOwnership _out308;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out309;
                    (this).GenExpr(_1568_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out307, out _out308, out _out309);
                    _1613_recursiveGen = _out307;
                    _1614___v108 = _out308;
                    _1615_recIdents = _out309;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1613_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out310;
                    DCOMP._IOwnership _out311;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out310, out _out311);
                    r = _out310;
                    resultingOwnership = _out311;
                    readIdents = _1615_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched76) {
          DAST._IType _09 = _source76.dtor__0;
          if (_09.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1616___v109 = _09.dtor_Passthrough_a0;
            DAST._IType _19 = _source76.dtor__1;
            if (_19.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1617___v110 = _19.dtor_Passthrough_a0;
              unmatched76 = false;
              {
                RAST._IExpr _1618_recursiveGen;
                DCOMP._IOwnership _1619___v111;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1620_recIdents;
                RAST._IExpr _out312;
                DCOMP._IOwnership _out313;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out314;
                (this).GenExpr(_1568_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out312, out _out313, out _out314);
                _1618_recursiveGen = _out312;
                _1619___v111 = _out313;
                _1620_recIdents = _out314;
                RAST._IType _1621_toTpeGen;
                RAST._IType _out315;
                _out315 = (this).GenType(_1570_toTpe, true, false);
                _1621_toTpeGen = _out315;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1618_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1621_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out316;
                DCOMP._IOwnership _out317;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out316, out _out317);
                r = _out316;
                resultingOwnership = _out317;
                readIdents = _1620_recIdents;
              }
            }
          }
        }
        if (unmatched76) {
          _System._ITuple2<DAST._IType, DAST._IType> _1622___v112 = _source76;
          unmatched76 = false;
          {
            RAST._IExpr _out318;
            DCOMP._IOwnership _out319;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out320;
            (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out318, out _out319, out _out320);
            r = _out318;
            resultingOwnership = _out319;
            readIdents = _out320;
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
      Std.Wrappers._IOption<RAST._IType> _1623_tpe;
      _1623_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1624_placeboOpt;
      _1624_placeboOpt = (((_1623_tpe).is_Some) ? (((_1623_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _1625_currentlyBorrowed;
      _1625_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1626_noNeedOfClone;
      _1626_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1624_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _1625_currentlyBorrowed = false;
        _1626_noNeedOfClone = true;
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        r = RAST.__default.BorrowMut(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        if (!(_1626_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1626_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1625_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        r = RAST.__default.Borrow(r);
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
      DAST._IExpression _source77 = e;
      bool unmatched77 = true;
      if (unmatched77) {
        if (_source77.is_Literal) {
          DAST._ILiteral _1627___v113 = _source77.dtor_Literal_a0;
          unmatched77 = false;
          RAST._IExpr _out321;
          DCOMP._IOwnership _out322;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out323;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out321, out _out322, out _out323);
          r = _out321;
          resultingOwnership = _out322;
          readIdents = _out323;
        }
      }
      if (unmatched77) {
        if (_source77.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1628_name = _source77.dtor_Ident_a0;
          unmatched77 = false;
          {
            RAST._IExpr _out324;
            DCOMP._IOwnership _out325;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out326;
            (this).GenIdent(DCOMP.__default.escapeName(_1628_name), selfIdent, env, expectedOwnership, out _out324, out _out325, out _out326);
            r = _out324;
            resultingOwnership = _out325;
            readIdents = _out326;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1629_path = _source77.dtor_Companion_a0;
          unmatched77 = false;
          {
            RAST._IExpr _out327;
            _out327 = DCOMP.COMP.GenPathExpr(_1629_path);
            r = _out327;
            if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else {
              RAST._IExpr _out328;
              DCOMP._IOwnership _out329;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out328, out _out329);
              r = _out328;
              resultingOwnership = _out329;
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_InitializationValue) {
          DAST._IType _1630_typ = _source77.dtor_typ;
          unmatched77 = false;
          {
            RAST._IType _1631_typExpr;
            RAST._IType _out330;
            _out330 = (this).GenType(_1630_typ, false, false);
            _1631_typExpr = _out330;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1631_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
            RAST._IExpr _out331;
            DCOMP._IOwnership _out332;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out331, out _out332);
            r = _out331;
            resultingOwnership = _out332;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _1632_values = _source77.dtor_Tuple_a0;
          unmatched77 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1633_exprs;
            _1633_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi30 = new BigInteger((_1632_values).Count);
            for (BigInteger _1634_i = BigInteger.Zero; _1634_i < _hi30; _1634_i++) {
              RAST._IExpr _1635_recursiveGen;
              DCOMP._IOwnership _1636___v114;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1637_recIdents;
              RAST._IExpr _out333;
              DCOMP._IOwnership _out334;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out335;
              (this).GenExpr((_1632_values).Select(_1634_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out333, out _out334, out _out335);
              _1635_recursiveGen = _out333;
              _1636___v114 = _out334;
              _1637_recIdents = _out335;
              _1633_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1633_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1635_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1637_recIdents);
            }
            r = (((new BigInteger((_1632_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_1633_exprs)) : (RAST.__default.SystemTuple(_1633_exprs)));
            RAST._IExpr _out336;
            DCOMP._IOwnership _out337;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out336, out _out337);
            r = _out336;
            resultingOwnership = _out337;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1638_path = _source77.dtor_path;
          Dafny.ISequence<DAST._IType> _1639_typeArgs = _source77.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1640_args = _source77.dtor_args;
          unmatched77 = false;
          {
            RAST._IExpr _out338;
            _out338 = DCOMP.COMP.GenPathExpr(_1638_path);
            r = _out338;
            if ((new BigInteger((_1639_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1641_typeExprs;
              _1641_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi31 = new BigInteger((_1639_typeArgs).Count);
              for (BigInteger _1642_i = BigInteger.Zero; _1642_i < _hi31; _1642_i++) {
                RAST._IType _1643_typeExpr;
                RAST._IType _out339;
                _out339 = (this).GenType((_1639_typeArgs).Select(_1642_i), false, false);
                _1643_typeExpr = _out339;
                _1641_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1641_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1643_typeExpr));
              }
              r = (r).ApplyType(_1641_typeExprs);
            }
            r = (r).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1644_arguments;
            _1644_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi32 = new BigInteger((_1640_args).Count);
            for (BigInteger _1645_i = BigInteger.Zero; _1645_i < _hi32; _1645_i++) {
              RAST._IExpr _1646_recursiveGen;
              DCOMP._IOwnership _1647___v115;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1648_recIdents;
              RAST._IExpr _out340;
              DCOMP._IOwnership _out341;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out342;
              (this).GenExpr((_1640_args).Select(_1645_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out340, out _out341, out _out342);
              _1646_recursiveGen = _out340;
              _1647___v115 = _out341;
              _1648_recIdents = _out342;
              _1644_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1644_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1646_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1648_recIdents);
            }
            r = (r).Apply(_1644_arguments);
            RAST._IExpr _out343;
            DCOMP._IOwnership _out344;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out343, out _out344);
            r = _out343;
            resultingOwnership = _out344;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_NewArray) {
          Dafny.ISequence<DAST._IExpression> _1649_dims = _source77.dtor_dims;
          DAST._IType _1650_typ = _source77.dtor_typ;
          unmatched77 = false;
          {
            BigInteger _1651_i;
            _1651_i = (new BigInteger((_1649_dims).Count)) - (BigInteger.One);
            RAST._IType _1652_genTyp;
            RAST._IType _out345;
            _out345 = (this).GenType(_1650_typ, false, false);
            _1652_genTyp = _out345;
            Dafny.ISequence<Dafny.Rune> _1653_s;
            _1653_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1652_genTyp)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::std::default::Default>::default()"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            while ((_1651_i).Sign != -1) {
              RAST._IExpr _1654_recursiveGen;
              DCOMP._IOwnership _1655___v116;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1656_recIdents;
              RAST._IExpr _out346;
              DCOMP._IOwnership _out347;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out348;
              (this).GenExpr((_1649_dims).Select(_1651_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out346, out _out347, out _out348);
              _1654_recursiveGen = _out346;
              _1655___v116 = _out347;
              _1656_recIdents = _out348;
              _1653_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), _1653_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), (_1654_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1656_recIdents);
              _1651_i = (_1651_i) - (BigInteger.One);
            }
            r = RAST.Expr.create_RawExpr(_1653_s);
            RAST._IExpr _out349;
            DCOMP._IOwnership _out350;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out349, out _out350);
            r = _out349;
            resultingOwnership = _out350;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_DatatypeValue) {
          DAST._IDatatypeType _1657_datatypeType = _source77.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1658_typeArgs = _source77.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1659_variant = _source77.dtor_variant;
          bool _1660_isCo = _source77.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1661_values = _source77.dtor_contents;
          unmatched77 = false;
          {
            RAST._IExpr _out351;
            _out351 = DCOMP.COMP.GenPathExpr((_1657_datatypeType).dtor_path);
            r = _out351;
            Dafny.ISequence<RAST._IType> _1662_genTypeArgs;
            _1662_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi33 = new BigInteger((_1658_typeArgs).Count);
            for (BigInteger _1663_i = BigInteger.Zero; _1663_i < _hi33; _1663_i++) {
              RAST._IType _1664_typeExpr;
              RAST._IType _out352;
              _out352 = (this).GenType((_1658_typeArgs).Select(_1663_i), false, false);
              _1664_typeExpr = _out352;
              _1662_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1662_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1664_typeExpr));
            }
            if ((new BigInteger((_1658_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1662_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1659_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1665_assignments;
            _1665_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi34 = new BigInteger((_1661_values).Count);
            for (BigInteger _1666_i = BigInteger.Zero; _1666_i < _hi34; _1666_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs63 = (_1661_values).Select(_1666_i);
              Dafny.ISequence<Dafny.Rune> _1667_name = _let_tmp_rhs63.dtor__0;
              DAST._IExpression _1668_value = _let_tmp_rhs63.dtor__1;
              if (_1660_isCo) {
                RAST._IExpr _1669_recursiveGen;
                DCOMP._IOwnership _1670___v117;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1671_recIdents;
                RAST._IExpr _out353;
                DCOMP._IOwnership _out354;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out355;
                (this).GenExpr(_1668_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out353, out _out354, out _out355);
                _1669_recursiveGen = _out353;
                _1670___v117 = _out354;
                _1671_recIdents = _out355;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1671_recIdents);
                Dafny.ISequence<Dafny.Rune> _1672_allReadCloned;
                _1672_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1671_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1673_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1671_recIdents).Elements) {
                    _1673_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1671_recIdents).Contains(_1673_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 3398)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1672_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1672_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1673_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1673_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1671_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1671_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1673_next));
                }
                Dafny.ISequence<Dafny.Rune> _1674_wasAssigned;
                _1674_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1672_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1669_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1665_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1665_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1667_name, RAST.Expr.create_RawExpr(_1674_wasAssigned))));
              } else {
                RAST._IExpr _1675_recursiveGen;
                DCOMP._IOwnership _1676___v118;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1677_recIdents;
                RAST._IExpr _out356;
                DCOMP._IOwnership _out357;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out358;
                (this).GenExpr(_1668_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out356, out _out357, out _out358);
                _1675_recursiveGen = _out356;
                _1676___v118 = _out357;
                _1677_recIdents = _out358;
                _1665_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1665_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1667_name, _1675_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1677_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1665_assignments);
            if ((this).IsRcWrapped((_1657_datatypeType).dtor_attributes)) {
              r = RAST.__default.RcNew(r);
            }
            RAST._IExpr _out359;
            DCOMP._IOwnership _out360;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out359, out _out360);
            r = _out359;
            resultingOwnership = _out360;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Convert) {
          DAST._IExpression _1678___v119 = _source77.dtor_value;
          DAST._IType _1679___v120 = _source77.dtor_from;
          DAST._IType _1680___v121 = _source77.dtor_typ;
          unmatched77 = false;
          {
            RAST._IExpr _out361;
            DCOMP._IOwnership _out362;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out363;
            (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out361, out _out362, out _out363);
            r = _out361;
            resultingOwnership = _out362;
            readIdents = _out363;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_SeqConstruct) {
          DAST._IExpression _1681_length = _source77.dtor_length;
          DAST._IExpression _1682_expr = _source77.dtor_elem;
          unmatched77 = false;
          {
            RAST._IExpr _1683_recursiveGen;
            DCOMP._IOwnership _1684___v122;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1685_recIdents;
            RAST._IExpr _out364;
            DCOMP._IOwnership _out365;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out366;
            (this).GenExpr(_1682_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out364, out _out365, out _out366);
            _1683_recursiveGen = _out364;
            _1684___v122 = _out365;
            _1685_recIdents = _out366;
            RAST._IExpr _1686_lengthGen;
            DCOMP._IOwnership _1687___v123;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1688_lengthIdents;
            RAST._IExpr _out367;
            DCOMP._IOwnership _out368;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out369;
            (this).GenExpr(_1681_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out367, out _out368, out _out369);
            _1686_lengthGen = _out367;
            _1687___v123 = _out368;
            _1688_lengthIdents = _out369;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1683_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1686_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1685_recIdents, _1688_lengthIdents);
            RAST._IExpr _out370;
            DCOMP._IOwnership _out371;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out370, out _out371);
            r = _out370;
            resultingOwnership = _out371;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _1689_exprs = _source77.dtor_elements;
          DAST._IType _1690_typ = _source77.dtor_typ;
          unmatched77 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1691_genTpe;
            RAST._IType _out372;
            _out372 = (this).GenType(_1690_typ, false, false);
            _1691_genTpe = _out372;
            BigInteger _1692_i;
            _1692_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1693_args;
            _1693_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1692_i) < (new BigInteger((_1689_exprs).Count))) {
              RAST._IExpr _1694_recursiveGen;
              DCOMP._IOwnership _1695___v124;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1696_recIdents;
              RAST._IExpr _out373;
              DCOMP._IOwnership _out374;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out375;
              (this).GenExpr((_1689_exprs).Select(_1692_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out373, out _out374, out _out375);
              _1694_recursiveGen = _out373;
              _1695___v124 = _out374;
              _1696_recIdents = _out375;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1696_recIdents);
              _1693_args = Dafny.Sequence<RAST._IExpr>.Concat(_1693_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1694_recursiveGen));
              _1692_i = (_1692_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_1693_args);
            if ((new BigInteger((_1693_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1691_genTpe));
            }
            RAST._IExpr _out376;
            DCOMP._IOwnership _out377;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out376, out _out377);
            r = _out376;
            resultingOwnership = _out377;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _1697_exprs = _source77.dtor_elements;
          unmatched77 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1698_generatedValues;
            _1698_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1699_i;
            _1699_i = BigInteger.Zero;
            while ((_1699_i) < (new BigInteger((_1697_exprs).Count))) {
              RAST._IExpr _1700_recursiveGen;
              DCOMP._IOwnership _1701___v125;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1702_recIdents;
              RAST._IExpr _out378;
              DCOMP._IOwnership _out379;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out380;
              (this).GenExpr((_1697_exprs).Select(_1699_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out378, out _out379, out _out380);
              _1700_recursiveGen = _out378;
              _1701___v125 = _out379;
              _1702_recIdents = _out380;
              _1698_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1698_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1700_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1702_recIdents);
              _1699_i = (_1699_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_1698_generatedValues);
            RAST._IExpr _out381;
            DCOMP._IOwnership _out382;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out381, out _out382);
            r = _out381;
            resultingOwnership = _out382;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _1703_exprs = _source77.dtor_elements;
          unmatched77 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1704_generatedValues;
            _1704_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1705_i;
            _1705_i = BigInteger.Zero;
            while ((_1705_i) < (new BigInteger((_1703_exprs).Count))) {
              RAST._IExpr _1706_recursiveGen;
              DCOMP._IOwnership _1707___v126;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1708_recIdents;
              RAST._IExpr _out383;
              DCOMP._IOwnership _out384;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out385;
              (this).GenExpr((_1703_exprs).Select(_1705_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out383, out _out384, out _out385);
              _1706_recursiveGen = _out383;
              _1707___v126 = _out384;
              _1708_recIdents = _out385;
              _1704_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1704_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1706_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1708_recIdents);
              _1705_i = (_1705_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_1704_generatedValues);
            RAST._IExpr _out386;
            DCOMP._IOwnership _out387;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out386, out _out387);
            r = _out386;
            resultingOwnership = _out387;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_ToMultiset) {
          DAST._IExpression _1709_expr = _source77.dtor_ToMultiset_a0;
          unmatched77 = false;
          {
            RAST._IExpr _1710_recursiveGen;
            DCOMP._IOwnership _1711___v127;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1712_recIdents;
            RAST._IExpr _out388;
            DCOMP._IOwnership _out389;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out390;
            (this).GenExpr(_1709_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out388, out _out389, out _out390);
            _1710_recursiveGen = _out388;
            _1711___v127 = _out389;
            _1712_recIdents = _out390;
            r = ((_1710_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _1712_recIdents;
            RAST._IExpr _out391;
            DCOMP._IOwnership _out392;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out391, out _out392);
            r = _out391;
            resultingOwnership = _out392;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1713_mapElems = _source77.dtor_mapElems;
          unmatched77 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1714_generatedValues;
            _1714_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1715_i;
            _1715_i = BigInteger.Zero;
            while ((_1715_i) < (new BigInteger((_1713_mapElems).Count))) {
              RAST._IExpr _1716_recursiveGenKey;
              DCOMP._IOwnership _1717___v128;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1718_recIdentsKey;
              RAST._IExpr _out393;
              DCOMP._IOwnership _out394;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out395;
              (this).GenExpr(((_1713_mapElems).Select(_1715_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out393, out _out394, out _out395);
              _1716_recursiveGenKey = _out393;
              _1717___v128 = _out394;
              _1718_recIdentsKey = _out395;
              RAST._IExpr _1719_recursiveGenValue;
              DCOMP._IOwnership _1720___v129;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1721_recIdentsValue;
              RAST._IExpr _out396;
              DCOMP._IOwnership _out397;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out398;
              (this).GenExpr(((_1713_mapElems).Select(_1715_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out396, out _out397, out _out398);
              _1719_recursiveGenValue = _out396;
              _1720___v129 = _out397;
              _1721_recIdentsValue = _out398;
              _1714_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1714_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1716_recursiveGenKey, _1719_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1718_recIdentsKey), _1721_recIdentsValue);
              _1715_i = (_1715_i) + (BigInteger.One);
            }
            _1715_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1722_arguments;
            _1722_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1715_i) < (new BigInteger((_1714_generatedValues).Count))) {
              RAST._IExpr _1723_genKey;
              _1723_genKey = ((_1714_generatedValues).Select(_1715_i)).dtor__0;
              RAST._IExpr _1724_genValue;
              _1724_genValue = ((_1714_generatedValues).Select(_1715_i)).dtor__1;
              _1722_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1722_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1723_genKey, _1724_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _1715_i = (_1715_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_1722_arguments);
            RAST._IExpr _out399;
            DCOMP._IOwnership _out400;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out399, out _out400);
            r = _out399;
            resultingOwnership = _out400;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_SeqUpdate) {
          DAST._IExpression _1725_expr = _source77.dtor_expr;
          DAST._IExpression _1726_index = _source77.dtor_indexExpr;
          DAST._IExpression _1727_value = _source77.dtor_value;
          unmatched77 = false;
          {
            RAST._IExpr _1728_exprR;
            DCOMP._IOwnership _1729___v130;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1730_exprIdents;
            RAST._IExpr _out401;
            DCOMP._IOwnership _out402;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
            (this).GenExpr(_1725_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out401, out _out402, out _out403);
            _1728_exprR = _out401;
            _1729___v130 = _out402;
            _1730_exprIdents = _out403;
            RAST._IExpr _1731_indexR;
            DCOMP._IOwnership _1732_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1733_indexIdents;
            RAST._IExpr _out404;
            DCOMP._IOwnership _out405;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out406;
            (this).GenExpr(_1726_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out404, out _out405, out _out406);
            _1731_indexR = _out404;
            _1732_indexOwnership = _out405;
            _1733_indexIdents = _out406;
            RAST._IExpr _1734_valueR;
            DCOMP._IOwnership _1735_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1736_valueIdents;
            RAST._IExpr _out407;
            DCOMP._IOwnership _out408;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
            (this).GenExpr(_1727_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out407, out _out408, out _out409);
            _1734_valueR = _out407;
            _1735_valueOwnership = _out408;
            _1736_valueIdents = _out409;
            r = ((_1728_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1731_indexR, _1734_valueR));
            RAST._IExpr _out410;
            DCOMP._IOwnership _out411;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out410, out _out411);
            r = _out410;
            resultingOwnership = _out411;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1730_exprIdents, _1733_indexIdents), _1736_valueIdents);
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_MapUpdate) {
          DAST._IExpression _1737_expr = _source77.dtor_expr;
          DAST._IExpression _1738_index = _source77.dtor_indexExpr;
          DAST._IExpression _1739_value = _source77.dtor_value;
          unmatched77 = false;
          {
            RAST._IExpr _1740_exprR;
            DCOMP._IOwnership _1741___v131;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1742_exprIdents;
            RAST._IExpr _out412;
            DCOMP._IOwnership _out413;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out414;
            (this).GenExpr(_1737_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out412, out _out413, out _out414);
            _1740_exprR = _out412;
            _1741___v131 = _out413;
            _1742_exprIdents = _out414;
            RAST._IExpr _1743_indexR;
            DCOMP._IOwnership _1744_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1745_indexIdents;
            RAST._IExpr _out415;
            DCOMP._IOwnership _out416;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out417;
            (this).GenExpr(_1738_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out415, out _out416, out _out417);
            _1743_indexR = _out415;
            _1744_indexOwnership = _out416;
            _1745_indexIdents = _out417;
            RAST._IExpr _1746_valueR;
            DCOMP._IOwnership _1747_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1748_valueIdents;
            RAST._IExpr _out418;
            DCOMP._IOwnership _out419;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out420;
            (this).GenExpr(_1739_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out418, out _out419, out _out420);
            _1746_valueR = _out418;
            _1747_valueOwnership = _out419;
            _1748_valueIdents = _out420;
            r = ((_1740_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1743_indexR, _1746_valueR));
            RAST._IExpr _out421;
            DCOMP._IOwnership _out422;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out421, out _out422);
            r = _out421;
            resultingOwnership = _out422;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1742_exprIdents, _1745_indexIdents), _1748_valueIdents);
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_This) {
          unmatched77 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source78 = selfIdent;
            bool unmatched78 = true;
            if (unmatched78) {
              if (_source78.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1749_id = _source78.dtor_value;
                unmatched78 = false;
                {
                  r = RAST.Expr.create_Identifier(_1749_id);
                  if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
                    r = RAST.__default.Clone(r);
                    resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
                  } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
                    r = RAST.__default.BoxNew(RAST.__default.Clone(r));
                    resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
                  } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
                    if (!(_1749_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                      r = RAST.__default.Borrow(r);
                    }
                    resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
                  } else {
                    if (!(_1749_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                      r = RAST.__default.BorrowMut(r);
                    }
                    resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
                  }
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1749_id);
                }
              }
            }
            if (unmatched78) {
              unmatched78 = false;
              {
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")"));
                RAST._IExpr _out423;
                DCOMP._IOwnership _out424;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out423, out _out424);
                r = _out423;
                resultingOwnership = _out424;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              }
            }
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Ite) {
          DAST._IExpression _1750_cond = _source77.dtor_cond;
          DAST._IExpression _1751_t = _source77.dtor_thn;
          DAST._IExpression _1752_f = _source77.dtor_els;
          unmatched77 = false;
          {
            RAST._IExpr _1753_cond;
            DCOMP._IOwnership _1754___v132;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1755_recIdentsCond;
            RAST._IExpr _out425;
            DCOMP._IOwnership _out426;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out427;
            (this).GenExpr(_1750_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out425, out _out426, out _out427);
            _1753_cond = _out425;
            _1754___v132 = _out426;
            _1755_recIdentsCond = _out427;
            Dafny.ISequence<Dafny.Rune> _1756_condString;
            _1756_condString = (_1753_cond)._ToString(DCOMP.__default.IND);
            RAST._IExpr _1757___v133;
            DCOMP._IOwnership _1758_tHasToBeOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1759___v134;
            RAST._IExpr _out428;
            DCOMP._IOwnership _out429;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out430;
            (this).GenExpr(_1751_t, selfIdent, env, expectedOwnership, out _out428, out _out429, out _out430);
            _1757___v133 = _out428;
            _1758_tHasToBeOwned = _out429;
            _1759___v134 = _out430;
            RAST._IExpr _1760_fExpr;
            DCOMP._IOwnership _1761_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1762_recIdentsF;
            RAST._IExpr _out431;
            DCOMP._IOwnership _out432;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out433;
            (this).GenExpr(_1752_f, selfIdent, env, _1758_tHasToBeOwned, out _out431, out _out432, out _out433);
            _1760_fExpr = _out431;
            _1761_fOwned = _out432;
            _1762_recIdentsF = _out433;
            Dafny.ISequence<Dafny.Rune> _1763_fString;
            _1763_fString = (_1760_fExpr)._ToString(DCOMP.__default.IND);
            RAST._IExpr _1764_tExpr;
            DCOMP._IOwnership _1765___v135;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1766_recIdentsT;
            RAST._IExpr _out434;
            DCOMP._IOwnership _out435;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out436;
            (this).GenExpr(_1751_t, selfIdent, env, _1761_fOwned, out _out434, out _out435, out _out436);
            _1764_tExpr = _out434;
            _1765___v135 = _out435;
            _1766_recIdentsT = _out436;
            Dafny.ISequence<Dafny.Rune> _1767_tString;
            _1767_tString = (_1764_tExpr)._ToString(DCOMP.__default.IND);
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _1756_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _1767_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _1763_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})")));
            RAST._IExpr _out437;
            DCOMP._IOwnership _out438;
            DCOMP.COMP.FromOwnership(r, _1761_fOwned, expectedOwnership, out _out437, out _out438);
            r = _out437;
            resultingOwnership = _out438;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1755_recIdentsCond, _1766_recIdentsT), _1762_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source77.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _1768_e = _source77.dtor_expr;
            DAST.Format._IUnaryOpFormat _1769_format = _source77.dtor_format1;
            unmatched77 = false;
            {
              RAST._IExpr _1770_recursiveGen;
              DCOMP._IOwnership _1771___v136;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1772_recIdents;
              RAST._IExpr _out439;
              DCOMP._IOwnership _out440;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out441;
              (this).GenExpr(_1768_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out439, out _out440, out _out441);
              _1770_recursiveGen = _out439;
              _1771___v136 = _out440;
              _1772_recIdents = _out441;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _1770_recursiveGen, _1769_format);
              RAST._IExpr _out442;
              DCOMP._IOwnership _out443;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out442, out _out443);
              r = _out442;
              resultingOwnership = _out443;
              readIdents = _1772_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source77.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _1773_e = _source77.dtor_expr;
            DAST.Format._IUnaryOpFormat _1774_format = _source77.dtor_format1;
            unmatched77 = false;
            {
              RAST._IExpr _1775_recursiveGen;
              DCOMP._IOwnership _1776___v137;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1777_recIdents;
              RAST._IExpr _out444;
              DCOMP._IOwnership _out445;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out446;
              (this).GenExpr(_1773_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out444, out _out445, out _out446);
              _1775_recursiveGen = _out444;
              _1776___v137 = _out445;
              _1777_recIdents = _out446;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _1775_recursiveGen, _1774_format);
              RAST._IExpr _out447;
              DCOMP._IOwnership _out448;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out447, out _out448);
              r = _out447;
              resultingOwnership = _out448;
              readIdents = _1777_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source77.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _1778_e = _source77.dtor_expr;
            DAST.Format._IUnaryOpFormat _1779_format = _source77.dtor_format1;
            unmatched77 = false;
            {
              RAST._IExpr _1780_recursiveGen;
              DCOMP._IOwnership _1781_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1782_recIdents;
              RAST._IExpr _out449;
              DCOMP._IOwnership _out450;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
              (this).GenExpr(_1778_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out449, out _out450, out _out451);
              _1780_recursiveGen = _out449;
              _1781_recOwned = _out450;
              _1782_recIdents = _out451;
              r = ((_1780_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out452;
              DCOMP._IOwnership _out453;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out452, out _out453);
              r = _out452;
              resultingOwnership = _out453;
              readIdents = _1782_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_BinOp) {
          DAST._IBinOp _1783___v138 = _source77.dtor_op;
          DAST._IExpression _1784___v139 = _source77.dtor_left;
          DAST._IExpression _1785___v140 = _source77.dtor_right;
          DAST.Format._IBinaryOpFormat _1786___v141 = _source77.dtor_format2;
          unmatched77 = false;
          RAST._IExpr _out454;
          DCOMP._IOwnership _out455;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out456;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out454, out _out455, out _out456);
          r = _out454;
          resultingOwnership = _out455;
          readIdents = _out456;
        }
      }
      if (unmatched77) {
        if (_source77.is_ArrayLen) {
          DAST._IExpression _1787_expr = _source77.dtor_expr;
          BigInteger _1788_dim = _source77.dtor_dim;
          unmatched77 = false;
          {
            RAST._IExpr _1789_recursiveGen;
            DCOMP._IOwnership _1790___v142;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1791_recIdents;
            RAST._IExpr _out457;
            DCOMP._IOwnership _out458;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out459;
            (this).GenExpr(_1787_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out457, out _out458, out _out459);
            _1789_recursiveGen = _out457;
            _1790___v142 = _out458;
            _1791_recIdents = _out459;
            if ((_1788_dim).Sign == 0) {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), (_1789_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())")));
            } else {
              Dafny.ISequence<Dafny.Rune> _1792_s;
              _1792_s = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(m.borrow().len())")))._ToString(DCOMP.__default.IND);
              BigInteger _1793_i;
              _1793_i = BigInteger.One;
              while ((_1793_i) < (_1788_dim)) {
                _1792_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("m.borrow().get(0).map(|m| "), _1792_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"));
                _1793_i = (_1793_i) + (BigInteger.One);
              }
              r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_1789_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow().get(0).map(|m| ")), _1792_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"))));
            }
            RAST._IExpr _out460;
            DCOMP._IOwnership _out461;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out460, out _out461);
            r = _out460;
            resultingOwnership = _out461;
            readIdents = _1791_recIdents;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_MapKeys) {
          DAST._IExpression _1794_expr = _source77.dtor_expr;
          unmatched77 = false;
          {
            RAST._IExpr _1795_recursiveGen;
            DCOMP._IOwnership _1796___v143;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1797_recIdents;
            RAST._IExpr _out462;
            DCOMP._IOwnership _out463;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out464;
            (this).GenExpr(_1794_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out462, out _out463, out _out464);
            _1795_recursiveGen = _out462;
            _1796___v143 = _out463;
            _1797_recIdents = _out464;
            readIdents = _1797_recIdents;
            r = ((_1795_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out465;
            DCOMP._IOwnership _out466;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out465, out _out466);
            r = _out465;
            resultingOwnership = _out466;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_MapValues) {
          DAST._IExpression _1798_expr = _source77.dtor_expr;
          unmatched77 = false;
          {
            RAST._IExpr _1799_recursiveGen;
            DCOMP._IOwnership _1800___v144;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1801_recIdents;
            RAST._IExpr _out467;
            DCOMP._IOwnership _out468;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out469;
            (this).GenExpr(_1798_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out467, out _out468, out _out469);
            _1799_recursiveGen = _out467;
            _1800___v144 = _out468;
            _1801_recIdents = _out469;
            readIdents = _1801_recIdents;
            r = ((_1799_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out470;
            DCOMP._IOwnership _out471;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out470, out _out471);
            r = _out470;
            resultingOwnership = _out471;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_SelectFn) {
          DAST._IExpression _1802_on = _source77.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1803_field = _source77.dtor_field;
          bool _1804_isDatatype = _source77.dtor_onDatatype;
          bool _1805_isStatic = _source77.dtor_isStatic;
          BigInteger _1806_arity = _source77.dtor_arity;
          unmatched77 = false;
          {
            RAST._IExpr _1807_onExpr;
            DCOMP._IOwnership _1808_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1809_recIdents;
            RAST._IExpr _out472;
            DCOMP._IOwnership _out473;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out474;
            (this).GenExpr(_1802_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out472, out _out473, out _out474);
            _1807_onExpr = _out472;
            _1808_onOwned = _out473;
            _1809_recIdents = _out474;
            Dafny.ISequence<Dafny.Rune> _1810_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _1811_onString;
            _1811_onString = (_1807_onExpr)._ToString(DCOMP.__default.IND);
            if (_1805_isStatic) {
              _1810_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1811_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_1803_field));
            } else {
              _1810_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _1810_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1810_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _1811_onString), ((object.Equals(_1808_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _1812_args;
              _1812_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _1813_i;
              _1813_i = BigInteger.Zero;
              while ((_1813_i) < (_1806_arity)) {
                if ((_1813_i).Sign == 1) {
                  _1812_args = Dafny.Sequence<Dafny.Rune>.Concat(_1812_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _1812_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1812_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_1813_i));
                _1813_i = (_1813_i) + (BigInteger.One);
              }
              _1810_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1810_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _1812_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _1810_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1810_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_1803_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1812_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _1810_s = Dafny.Sequence<Dafny.Rune>.Concat(_1810_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _1810_s = Dafny.Sequence<Dafny.Rune>.Concat(_1810_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _1814_typeShape;
            _1814_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _1815_i;
            _1815_i = BigInteger.Zero;
            while ((_1815_i) < (_1806_arity)) {
              if ((_1815_i).Sign == 1) {
                _1814_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1814_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _1814_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1814_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _1815_i = (_1815_i) + (BigInteger.One);
            }
            _1814_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1814_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _1810_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _1810_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _1814_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_1810_s);
            RAST._IExpr _out475;
            DCOMP._IOwnership _out476;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out475, out _out476);
            r = _out475;
            resultingOwnership = _out476;
            readIdents = _1809_recIdents;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Select) {
          DAST._IExpression expr0 = _source77.dtor_expr;
          if (expr0.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1816_c = expr0.dtor_Companion_a0;
            Dafny.ISequence<Dafny.Rune> _1817_field = _source77.dtor_field;
            bool _1818_isConstant = _source77.dtor_isConstant;
            bool _1819_isDatatype = _source77.dtor_onDatatype;
            DAST._IType _1820_fieldType = _source77.dtor_fieldType;
            unmatched77 = false;
            {
              RAST._IExpr _1821_onExpr;
              DCOMP._IOwnership _1822_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1823_recIdents;
              RAST._IExpr _out477;
              DCOMP._IOwnership _out478;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out479;
              (this).GenExpr(DAST.Expression.create_Companion(_1816_c), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out477, out _out478, out _out479);
              _1821_onExpr = _out477;
              _1822_onOwned = _out478;
              _1823_recIdents = _out479;
              r = ((_1821_onExpr).MSel(DCOMP.__default.escapeName(_1817_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out480;
              DCOMP._IOwnership _out481;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out480, out _out481);
              r = _out480;
              resultingOwnership = _out481;
              readIdents = _1823_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Select) {
          DAST._IExpression _1824_on = _source77.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1825_field = _source77.dtor_field;
          bool _1826_isConstant = _source77.dtor_isConstant;
          bool _1827_isDatatype = _source77.dtor_onDatatype;
          DAST._IType _1828_fieldType = _source77.dtor_fieldType;
          unmatched77 = false;
          {
            if (_1827_isDatatype) {
              RAST._IExpr _1829_onExpr;
              DCOMP._IOwnership _1830_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1831_recIdents;
              RAST._IExpr _out482;
              DCOMP._IOwnership _out483;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out484;
              (this).GenExpr(_1824_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out482, out _out483, out _out484);
              _1829_onExpr = _out482;
              _1830_onOwned = _out483;
              _1831_recIdents = _out484;
              r = ((_1829_onExpr).Sel(DCOMP.__default.escapeName(_1825_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _1832_typ;
              RAST._IType _out485;
              _out485 = (this).GenType(_1828_fieldType, false, false);
              _1832_typ = _out485;
              RAST._IExpr _out486;
              DCOMP._IOwnership _out487;
              DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out486, out _out487);
              r = _out486;
              resultingOwnership = _out487;
              readIdents = _1831_recIdents;
            } else {
              RAST._IExpr _1833_onExpr;
              DCOMP._IOwnership _1834_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1835_recIdents;
              RAST._IExpr _out488;
              DCOMP._IOwnership _out489;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out490;
              (this).GenExpr(_1824_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out488, out _out489, out _out490);
              _1833_onExpr = _out488;
              _1834_onOwned = _out489;
              _1835_recIdents = _out490;
              r = _1833_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_1825_field));
              if (_1826_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _1836_s;
                _1836_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_1833_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_1825_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_1836_s);
              }
              DCOMP._IOwnership _1837_fromOwnership;
              _1837_fromOwnership = ((_1826_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out491;
              DCOMP._IOwnership _out492;
              DCOMP.COMP.FromOwnership(r, _1837_fromOwnership, expectedOwnership, out _out491, out _out492);
              r = _out491;
              resultingOwnership = _out492;
              readIdents = _1835_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Index) {
          DAST._IExpression _1838_on = _source77.dtor_expr;
          DAST._ICollKind _1839_collKind = _source77.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _1840_indices = _source77.dtor_indices;
          unmatched77 = false;
          {
            RAST._IExpr _1841_onExpr;
            DCOMP._IOwnership _1842_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1843_recIdents;
            RAST._IExpr _out493;
            DCOMP._IOwnership _out494;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out495;
            (this).GenExpr(_1838_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out493, out _out494, out _out495);
            _1841_onExpr = _out493;
            _1842_onOwned = _out494;
            _1843_recIdents = _out495;
            readIdents = _1843_recIdents;
            r = _1841_onExpr;
            BigInteger _1844_i;
            _1844_i = BigInteger.Zero;
            while ((_1844_i) < (new BigInteger((_1840_indices).Count))) {
              if (object.Equals(_1839_collKind, DAST.CollKind.create_Array())) {
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              RAST._IExpr _1845_idx;
              DCOMP._IOwnership _1846_idxOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1847_recIdentsIdx;
              RAST._IExpr _out496;
              DCOMP._IOwnership _out497;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out498;
              (this).GenExpr((_1840_indices).Select(_1844_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out496, out _out497, out _out498);
              _1845_idx = _out496;
              _1846_idxOwned = _out497;
              _1847_recIdentsIdx = _out498;
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_1845_idx);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1847_recIdentsIdx);
              _1844_i = (_1844_i) + (BigInteger.One);
            }
            RAST._IExpr _out499;
            DCOMP._IOwnership _out500;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out499, out _out500);
            r = _out499;
            resultingOwnership = _out500;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_IndexRange) {
          DAST._IExpression _1848_on = _source77.dtor_expr;
          bool _1849_isArray = _source77.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _1850_low = _source77.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _1851_high = _source77.dtor_high;
          unmatched77 = false;
          {
            RAST._IExpr _1852_onExpr;
            DCOMP._IOwnership _1853_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1854_recIdents;
            RAST._IExpr _out501;
            DCOMP._IOwnership _out502;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out503;
            (this).GenExpr(_1848_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out501, out _out502, out _out503);
            _1852_onExpr = _out501;
            _1853_onOwned = _out502;
            _1854_recIdents = _out503;
            readIdents = _1854_recIdents;
            Dafny.ISequence<Dafny.Rune> _1855_methodName;
            _1855_methodName = (((_1850_low).is_Some) ? ((((_1851_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_1851_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _1856_arguments;
            _1856_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source79 = _1850_low;
            bool unmatched79 = true;
            if (unmatched79) {
              if (_source79.is_Some) {
                DAST._IExpression _1857_l = _source79.dtor_value;
                unmatched79 = false;
                {
                  RAST._IExpr _1858_lExpr;
                  DCOMP._IOwnership _1859___v145;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1860_recIdentsL;
                  RAST._IExpr _out504;
                  DCOMP._IOwnership _out505;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out506;
                  (this).GenExpr(_1857_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out504, out _out505, out _out506);
                  _1858_lExpr = _out504;
                  _1859___v145 = _out505;
                  _1860_recIdentsL = _out506;
                  _1856_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1856_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1858_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1860_recIdentsL);
                }
              }
            }
            if (unmatched79) {
              unmatched79 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source80 = _1851_high;
            bool unmatched80 = true;
            if (unmatched80) {
              if (_source80.is_Some) {
                DAST._IExpression _1861_h = _source80.dtor_value;
                unmatched80 = false;
                {
                  RAST._IExpr _1862_hExpr;
                  DCOMP._IOwnership _1863___v146;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1864_recIdentsH;
                  RAST._IExpr _out507;
                  DCOMP._IOwnership _out508;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out509;
                  (this).GenExpr(_1861_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out507, out _out508, out _out509);
                  _1862_hExpr = _out507;
                  _1863___v146 = _out508;
                  _1864_recIdentsH = _out509;
                  _1856_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1856_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1862_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1864_recIdentsH);
                }
              }
            }
            if (unmatched80) {
              unmatched80 = false;
            }
            r = _1852_onExpr;
            if (_1849_isArray) {
              if (!(_1855_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _1855_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1855_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _1855_methodName))).Apply(_1856_arguments);
            } else {
              if (!(_1855_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_1855_methodName)).Apply(_1856_arguments);
              }
            }
            RAST._IExpr _out510;
            DCOMP._IOwnership _out511;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out510, out _out511);
            r = _out510;
            resultingOwnership = _out511;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_TupleSelect) {
          DAST._IExpression _1865_on = _source77.dtor_expr;
          BigInteger _1866_idx = _source77.dtor_index;
          DAST._IType _1867_fieldType = _source77.dtor_fieldType;
          unmatched77 = false;
          {
            RAST._IExpr _1868_onExpr;
            DCOMP._IOwnership _1869_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1870_recIdents;
            RAST._IExpr _out512;
            DCOMP._IOwnership _out513;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out514;
            (this).GenExpr(_1865_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out512, out _out513, out _out514);
            _1868_onExpr = _out512;
            _1869_onOwnership = _out513;
            _1870_recIdents = _out514;
            Dafny.ISequence<Dafny.Rune> _1871_selName;
            _1871_selName = Std.Strings.__default.OfNat(_1866_idx);
            DAST._IType _source81 = _1867_fieldType;
            bool unmatched81 = true;
            if (unmatched81) {
              if (_source81.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1872_tps = _source81.dtor_Tuple_a0;
                unmatched81 = false;
                if (((_1867_fieldType).is_Tuple) && ((new BigInteger((_1872_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _1871_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1871_selName);
                }
              }
            }
            if (unmatched81) {
              DAST._IType _1873___v147 = _source81;
              unmatched81 = false;
            }
            r = (_1868_onExpr).Sel(_1871_selName);
            RAST._IExpr _out515;
            DCOMP._IOwnership _out516;
            DCOMP.COMP.FromOwnership(r, _1869_onOwnership, expectedOwnership, out _out515, out _out516);
            r = _out515;
            resultingOwnership = _out516;
            readIdents = _1870_recIdents;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Call) {
          DAST._IExpression _1874_on = _source77.dtor_on;
          DAST._ICallName _1875_name = _source77.dtor_callName;
          Dafny.ISequence<DAST._IType> _1876_typeArgs = _source77.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1877_args = _source77.dtor_args;
          unmatched77 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IExpr _1878_onExpr;
            DCOMP._IOwnership _1879___v148;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1880_recIdents;
            RAST._IExpr _out517;
            DCOMP._IOwnership _out518;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out519;
            (this).GenExpr(_1874_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out517, out _out518, out _out519);
            _1878_onExpr = _out517;
            _1879___v148 = _out518;
            _1880_recIdents = _out519;
            Dafny.ISequence<RAST._IType> _1881_typeExprs;
            _1881_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
            if ((new BigInteger((_1876_typeArgs).Count)) >= (BigInteger.One)) {
              BigInteger _hi35 = new BigInteger((_1876_typeArgs).Count);
              for (BigInteger _1882_typeI = BigInteger.Zero; _1882_typeI < _hi35; _1882_typeI++) {
                RAST._IType _1883_typeExpr;
                RAST._IType _out520;
                _out520 = (this).GenType((_1876_typeArgs).Select(_1882_typeI), false, false);
                _1883_typeExpr = _out520;
                _1881_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1881_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1883_typeExpr));
              }
            }
            Dafny.ISequence<RAST._IExpr> _1884_argExprs;
            _1884_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi36 = new BigInteger((_1877_args).Count);
            for (BigInteger _1885_i = BigInteger.Zero; _1885_i < _hi36; _1885_i++) {
              DCOMP._IOwnership _1886_argOwnership;
              _1886_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              if (((_1875_name).is_CallName) && ((_1885_i) < (new BigInteger((((_1875_name).dtor_signature)).Count)))) {
                RAST._IType _1887_tpe;
                RAST._IType _out521;
                _out521 = (this).GenType(((((_1875_name).dtor_signature)).Select(_1885_i)).dtor_typ, false, false);
                _1887_tpe = _out521;
                if ((_1887_tpe).CanReadWithoutClone()) {
                  _1886_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
                }
              }
              RAST._IExpr _1888_argExpr;
              DCOMP._IOwnership _1889___v149;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1890_argIdents;
              RAST._IExpr _out522;
              DCOMP._IOwnership _out523;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out524;
              (this).GenExpr((_1877_args).Select(_1885_i), selfIdent, env, _1886_argOwnership, out _out522, out _out523, out _out524);
              _1888_argExpr = _out522;
              _1889___v149 = _out523;
              _1890_argIdents = _out524;
              _1884_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1884_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1888_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1890_argIdents);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1880_recIdents);
            Dafny.ISequence<Dafny.Rune> _1891_renderedName;
            _1891_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
              DAST._ICallName _source82 = _1875_name;
              bool unmatched82 = true;
              if (unmatched82) {
                if (_source82.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _1892_ident = _source82.dtor_name;
                  Std.Wrappers._IOption<DAST._IType> _1893___v150 = _source82.dtor_onType;
                  Dafny.ISequence<DAST._IFormal> _1894___v151 = _source82.dtor_signature;
                  unmatched82 = false;
                  return DCOMP.__default.escapeName(_1892_ident);
                }
              }
              if (unmatched82) {
                bool disjunctiveMatch12 = false;
                if (_source82.is_MapBuilderAdd) {
                  disjunctiveMatch12 = true;
                }
                if (_source82.is_SetBuilderAdd) {
                  disjunctiveMatch12 = true;
                }
                if (disjunctiveMatch12) {
                  unmatched82 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                }
              }
              if (unmatched82) {
                bool disjunctiveMatch13 = false;
                disjunctiveMatch13 = true;
                disjunctiveMatch13 = true;
                if (disjunctiveMatch13) {
                  unmatched82 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                }
              }
              throw new System.Exception("unexpected control point");
            }))();
            DAST._IExpression _source83 = _1874_on;
            bool unmatched83 = true;
            if (unmatched83) {
              if (_source83.is_Companion) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1895___v152 = _source83.dtor_Companion_a0;
                unmatched83 = false;
                {
                  _1878_onExpr = (_1878_onExpr).MSel(_1891_renderedName);
                }
              }
            }
            if (unmatched83) {
              DAST._IExpression _1896___v153 = _source83;
              unmatched83 = false;
              {
                _1878_onExpr = (_1878_onExpr).Sel(_1891_renderedName);
              }
            }
            r = _1878_onExpr;
            if ((new BigInteger((_1881_typeExprs).Count)).Sign == 1) {
              r = (r).ApplyType(_1881_typeExprs);
            }
            r = (r).Apply(_1884_argExprs);
            RAST._IExpr _out525;
            DCOMP._IOwnership _out526;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out525, out _out526);
            r = _out525;
            resultingOwnership = _out526;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _1897_paramsDafny = _source77.dtor_params;
          DAST._IType _1898_retType = _source77.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _1899_body = _source77.dtor_body;
          unmatched77 = false;
          {
            Dafny.ISequence<RAST._IFormal> _1900_params;
            Dafny.ISequence<RAST._IFormal> _out527;
            _out527 = (this).GenParams(_1897_paramsDafny);
            _1900_params = _out527;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1901_paramNames;
            _1901_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1902_paramTypesMap;
            _1902_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi37 = new BigInteger((_1900_params).Count);
            for (BigInteger _1903_i = BigInteger.Zero; _1903_i < _hi37; _1903_i++) {
              Dafny.ISequence<Dafny.Rune> _1904_name;
              _1904_name = ((_1900_params).Select(_1903_i)).dtor_name;
              _1901_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1901_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1904_name));
              _1902_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1902_paramTypesMap, _1904_name, ((_1900_params).Select(_1903_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _1905_env;
            _1905_env = DCOMP.Environment.create(_1901_paramNames, _1902_paramTypesMap);
            RAST._IExpr _1906_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1907_recIdents;
            DCOMP._IEnvironment _1908___v154;
            RAST._IExpr _out528;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out529;
            DCOMP._IEnvironment _out530;
            (this).GenStmts(_1899_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), _1905_env, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out528, out _out529, out _out530);
            _1906_recursiveGen = _out528;
            _1907_recIdents = _out529;
            _1908___v154 = _out530;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _1907_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1907_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_1909_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll6 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in (_1909_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _1910_name = (Dafny.ISequence<Dafny.Rune>)_compr_6;
                if ((_1909_paramNames).Contains(_1910_name)) {
                  _coll6.Add(_1910_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll6);
            }))())(_1901_paramNames));
            RAST._IExpr _1911_allReadCloned;
            _1911_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_1907_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _1912_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_1907_recIdents).Elements) {
                _1912_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_1907_recIdents).Contains(_1912_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 3862)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) && ((_1912_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
                  _1911_allReadCloned = (_1911_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
                }
              } else if (!((_1901_paramNames).Contains(_1912_next))) {
                _1911_allReadCloned = (_1911_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1912_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.Expr.create_Identifier(_1912_next)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1912_next));
              }
              _1907_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1907_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1912_next));
            }
            RAST._IType _1913_retTypeGen;
            RAST._IType _out531;
            _out531 = (this).GenType(_1898_retType, false, true);
            _1913_retTypeGen = _out531;
            r = RAST.Expr.create_Block((_1911_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_1900_params, Std.Wrappers.Option<RAST._IType>.create_Some(_1913_retTypeGen), RAST.Expr.create_Block(_1906_recursiveGen)))));
            RAST._IExpr _out532;
            DCOMP._IOwnership _out533;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out532, out _out533);
            r = _out532;
            resultingOwnership = _out533;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _1914_values = _source77.dtor_values;
          DAST._IType _1915_retType = _source77.dtor_retType;
          DAST._IExpression _1916_expr = _source77.dtor_expr;
          unmatched77 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1917_paramNames;
            _1917_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _1918_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out534;
            _out534 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_1919_value) => {
              return (_1919_value).dtor__0;
            })), _1914_values));
            _1918_paramFormals = _out534;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1920_paramTypes;
            _1920_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1921_paramNamesSet;
            _1921_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi38 = new BigInteger((_1914_values).Count);
            for (BigInteger _1922_i = BigInteger.Zero; _1922_i < _hi38; _1922_i++) {
              Dafny.ISequence<Dafny.Rune> _1923_name;
              _1923_name = (((_1914_values).Select(_1922_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _1924_rName;
              _1924_rName = DCOMP.__default.escapeName(_1923_name);
              _1917_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1917_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1924_rName));
              _1920_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1920_paramTypes, _1924_rName, ((_1918_paramFormals).Select(_1922_i)).dtor_tpe);
              _1921_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1921_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1924_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi39 = new BigInteger((_1914_values).Count);
            for (BigInteger _1925_i = BigInteger.Zero; _1925_i < _hi39; _1925_i++) {
              RAST._IType _1926_typeGen;
              RAST._IType _out535;
              _out535 = (this).GenType((((_1914_values).Select(_1925_i)).dtor__0).dtor_typ, false, true);
              _1926_typeGen = _out535;
              RAST._IExpr _1927_valueGen;
              DCOMP._IOwnership _1928___v155;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1929_recIdents;
              RAST._IExpr _out536;
              DCOMP._IOwnership _out537;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out538;
              (this).GenExpr(((_1914_values).Select(_1925_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out536, out _out537, out _out538);
              _1927_valueGen = _out536;
              _1928___v155 = _out537;
              _1929_recIdents = _out538;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_1914_values).Select(_1925_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1926_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1927_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1929_recIdents);
            }
            DCOMP._IEnvironment _1930_newEnv;
            _1930_newEnv = DCOMP.Environment.create(_1917_paramNames, _1920_paramTypes);
            RAST._IExpr _1931_recGen;
            DCOMP._IOwnership _1932_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1933_recIdents;
            RAST._IExpr _out539;
            DCOMP._IOwnership _out540;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
            (this).GenExpr(_1916_expr, selfIdent, _1930_newEnv, expectedOwnership, out _out539, out _out540, out _out541);
            _1931_recGen = _out539;
            _1932_recOwned = _out540;
            _1933_recIdents = _out541;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1933_recIdents, _1921_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_1931_recGen));
            RAST._IExpr _out542;
            DCOMP._IOwnership _out543;
            DCOMP.COMP.FromOwnership(r, _1932_recOwned, expectedOwnership, out _out542, out _out543);
            r = _out542;
            resultingOwnership = _out543;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _1934_name = _source77.dtor_name;
          DAST._IType _1935_tpe = _source77.dtor_typ;
          DAST._IExpression _1936_value = _source77.dtor_value;
          DAST._IExpression _1937_iifeBody = _source77.dtor_iifeBody;
          unmatched77 = false;
          {
            RAST._IExpr _1938_valueGen;
            DCOMP._IOwnership _1939___v156;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1940_recIdents;
            RAST._IExpr _out544;
            DCOMP._IOwnership _out545;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out546;
            (this).GenExpr(_1936_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out544, out _out545, out _out546);
            _1938_valueGen = _out544;
            _1939___v156 = _out545;
            _1940_recIdents = _out546;
            readIdents = _1940_recIdents;
            RAST._IType _1941_valueTypeGen;
            RAST._IType _out547;
            _out547 = (this).GenType(_1935_tpe, false, true);
            _1941_valueTypeGen = _out547;
            RAST._IExpr _1942_bodyGen;
            DCOMP._IOwnership _1943___v157;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1944_bodyIdents;
            RAST._IExpr _out548;
            DCOMP._IOwnership _out549;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out550;
            (this).GenExpr(_1937_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out548, out _out549, out _out550);
            _1942_bodyGen = _out548;
            _1943___v157 = _out549;
            _1944_bodyIdents = _out550;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1944_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_1934_name)))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_1934_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_1941_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1938_valueGen))).Then(_1942_bodyGen));
            RAST._IExpr _out551;
            DCOMP._IOwnership _out552;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out551, out _out552);
            r = _out551;
            resultingOwnership = _out552;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Apply) {
          DAST._IExpression _1945_func = _source77.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _1946_args = _source77.dtor_args;
          unmatched77 = false;
          {
            RAST._IExpr _1947_funcExpr;
            DCOMP._IOwnership _1948___v158;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1949_recIdents;
            RAST._IExpr _out553;
            DCOMP._IOwnership _out554;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out555;
            (this).GenExpr(_1945_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out553, out _out554, out _out555);
            _1947_funcExpr = _out553;
            _1948___v158 = _out554;
            _1949_recIdents = _out555;
            readIdents = _1949_recIdents;
            Dafny.ISequence<RAST._IExpr> _1950_rArgs;
            _1950_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi40 = new BigInteger((_1946_args).Count);
            for (BigInteger _1951_i = BigInteger.Zero; _1951_i < _hi40; _1951_i++) {
              RAST._IExpr _1952_argExpr;
              DCOMP._IOwnership _1953_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1954_argIdents;
              RAST._IExpr _out556;
              DCOMP._IOwnership _out557;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out558;
              (this).GenExpr((_1946_args).Select(_1951_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out556, out _out557, out _out558);
              _1952_argExpr = _out556;
              _1953_argOwned = _out557;
              _1954_argIdents = _out558;
              _1950_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1950_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1952_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1954_argIdents);
            }
            r = (_1947_funcExpr).Apply(_1950_rArgs);
            RAST._IExpr _out559;
            DCOMP._IOwnership _out560;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out559, out _out560);
            r = _out559;
            resultingOwnership = _out560;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_TypeTest) {
          DAST._IExpression _1955_on = _source77.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1956_dType = _source77.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _1957_variant = _source77.dtor_variant;
          unmatched77 = false;
          {
            RAST._IExpr _1958_exprGen;
            DCOMP._IOwnership _1959___v159;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1960_recIdents;
            RAST._IExpr _out561;
            DCOMP._IOwnership _out562;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out563;
            (this).GenExpr(_1955_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out561, out _out562, out _out563);
            _1958_exprGen = _out561;
            _1959___v159 = _out562;
            _1960_recIdents = _out563;
            RAST._IType _1961_dTypePath;
            RAST._IType _out564;
            _out564 = DCOMP.COMP.GenPath(_1956_dType);
            _1961_dTypePath = _out564;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_1958_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_1961_dTypePath).MSel(DCOMP.__default.escapeName(_1957_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out565;
            DCOMP._IOwnership _out566;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out565, out _out566);
            r = _out565;
            resultingOwnership = _out566;
            readIdents = _1960_recIdents;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_BoolBoundedPool) {
          unmatched77 = false;
          {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
            RAST._IExpr _out567;
            DCOMP._IOwnership _out568;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out567, out _out568);
            r = _out567;
            resultingOwnership = _out568;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_SetBoundedPool) {
          DAST._IExpression _1962_of = _source77.dtor_of;
          unmatched77 = false;
          {
            RAST._IExpr _1963_exprGen;
            DCOMP._IOwnership _1964___v160;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1965_recIdents;
            RAST._IExpr _out569;
            DCOMP._IOwnership _out570;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out571;
            (this).GenExpr(_1962_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out569, out _out570, out _out571);
            _1963_exprGen = _out569;
            _1964___v160 = _out570;
            _1965_recIdents = _out571;
            r = ((((_1963_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out572;
            DCOMP._IOwnership _out573;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out572, out _out573);
            r = _out572;
            resultingOwnership = _out573;
            readIdents = _1965_recIdents;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_SeqBoundedPool) {
          DAST._IExpression _1966_of = _source77.dtor_of;
          bool _1967_includeDuplicates = _source77.dtor_includeDuplicates;
          unmatched77 = false;
          {
            RAST._IExpr _1968_exprGen;
            DCOMP._IOwnership _1969___v161;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1970_recIdents;
            RAST._IExpr _out574;
            DCOMP._IOwnership _out575;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out576;
            (this).GenExpr(_1966_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out574, out _out575, out _out576);
            _1968_exprGen = _out574;
            _1969___v161 = _out575;
            _1970_recIdents = _out576;
            r = ((_1968_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_1967_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out577;
            DCOMP._IOwnership _out578;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out577, out _out578);
            r = _out577;
            resultingOwnership = _out578;
            readIdents = _1970_recIdents;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_IntRange) {
          DAST._IExpression _1971_lo = _source77.dtor_lo;
          DAST._IExpression _1972_hi = _source77.dtor_hi;
          bool _1973_up = _source77.dtor_up;
          unmatched77 = false;
          {
            RAST._IExpr _1974_lo;
            DCOMP._IOwnership _1975___v162;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1976_recIdentsLo;
            RAST._IExpr _out579;
            DCOMP._IOwnership _out580;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out581;
            (this).GenExpr(_1971_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out579, out _out580, out _out581);
            _1974_lo = _out579;
            _1975___v162 = _out580;
            _1976_recIdentsLo = _out581;
            RAST._IExpr _1977_hi;
            DCOMP._IOwnership _1978___v163;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1979_recIdentsHi;
            RAST._IExpr _out582;
            DCOMP._IOwnership _out583;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out584;
            (this).GenExpr(_1972_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out582, out _out583, out _out584);
            _1977_hi = _out582;
            _1978___v163 = _out583;
            _1979_recIdentsHi = _out584;
            if (_1973_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1974_lo, _1977_hi));
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1977_hi, _1974_lo));
            }
            RAST._IExpr _out585;
            DCOMP._IOwnership _out586;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out585, out _out586);
            r = _out585;
            resultingOwnership = _out586;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1976_recIdentsLo, _1979_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_UnboundedIntRange) {
          DAST._IExpression _1980_start = _source77.dtor_start;
          bool _1981_up = _source77.dtor_up;
          unmatched77 = false;
          {
            RAST._IExpr _1982_start;
            DCOMP._IOwnership _1983___v164;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1984_recIdentStart;
            RAST._IExpr _out587;
            DCOMP._IOwnership _out588;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out589;
            (this).GenExpr(_1980_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out587, out _out588, out _out589);
            _1982_start = _out587;
            _1983___v164 = _out588;
            _1984_recIdentStart = _out589;
            if (_1981_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).Apply1(_1982_start);
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).Apply1(_1982_start);
            }
            RAST._IExpr _out590;
            DCOMP._IOwnership _out591;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out590, out _out591);
            r = _out590;
            resultingOwnership = _out591;
            readIdents = _1984_recIdentStart;
            return ;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_MapBuilder) {
          DAST._IType _1985_keyType = _source77.dtor_keyType;
          DAST._IType _1986_valueType = _source77.dtor_valueType;
          unmatched77 = false;
          {
            RAST._IType _1987_kType;
            RAST._IType _out592;
            _out592 = (this).GenType(_1985_keyType, false, false);
            _1987_kType = _out592;
            RAST._IType _1988_vType;
            RAST._IType _out593;
            _out593 = (this).GenType(_1986_valueType, false, false);
            _1988_vType = _out593;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1987_kType, _1988_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out594;
            DCOMP._IOwnership _out595;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out594, out _out595);
            r = _out594;
            resultingOwnership = _out595;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched77) {
        DAST._IType _1989_elemType = _source77.dtor_elemType;
        unmatched77 = false;
        {
          RAST._IType _1990_eType;
          RAST._IType _out596;
          _out596 = (this).GenType(_1989_elemType, false, false);
          _1990_eType = _out596;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1990_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out597;
          DCOMP._IOwnership _out598;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out597, out _out598);
          r = _out597;
          resultingOwnership = _out598;
          return ;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      BigInteger _1991_i;
      _1991_i = BigInteger.Zero;
      while ((_1991_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _1992_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _1993_m;
        RAST._IMod _out599;
        _out599 = (this).GenModule((p).Select(_1991_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _1993_m = _out599;
        _1992_generated = (_1993_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_1991_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _1992_generated);
        _1991_i = (_1991_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _1994_i;
      _1994_i = BigInteger.Zero;
      while ((_1994_i) < (new BigInteger((fullName).Count))) {
        if ((_1994_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_1994_i)));
        _1994_i = (_1994_i) + (BigInteger.One);
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
    public static Dafny.IMap<DAST._IBinOp,Dafny.ISequence<Dafny.Rune>> OpTable { get {
      return Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.FromElements(new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Mod(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_And(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Or(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("||")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Div(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Lt(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_LtChar(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Plus(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Minus(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Times(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseAnd(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseOr(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseXor(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftRight(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftLeft(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<")));
    } }
  }
} // end of namespace DCOMP