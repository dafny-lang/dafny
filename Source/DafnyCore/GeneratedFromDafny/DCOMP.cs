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
      Dafny.ISequence<Dafny.Rune> _1037___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1037___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1037___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1037___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in123 = (i).Drop(new BigInteger(2));
        i = _in123;
        goto TAIL_CALL_START;
      } else {
        _1037___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1037___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in124 = (i).Drop(BigInteger.One);
        i = _in124;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1038___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1038___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1038___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1038___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in125 = (i).Drop(BigInteger.One);
        i = _in125;
        goto TAIL_CALL_START;
      } else {
        _1038___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1038___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _1039_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1039_r);
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
      BigInteger _1040_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1040_indexInEnv), ((this).dtor_names).Drop((_1040_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
      Dafny.ISequence<Dafny.Rune> _1041_modName;
      _1041_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_1041_modName);
      } else {
        Dafny.ISequence<RAST._IModDecl> _1042_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _1042_body = _out15;
        s = RAST.Mod.create_Mod(_1041_modName, _1042_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi5 = new BigInteger((body).Count);
      for (BigInteger _1043_i = BigInteger.Zero; _1043_i < _hi5; _1043_i++) {
        Dafny.ISequence<RAST._IModDecl> _1044_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source44 = (body).Select(_1043_i);
        bool unmatched44 = true;
        if (unmatched44) {
          if (_source44.is_Module) {
            DAST._IModule _1045_m = _source44.dtor_Module_a0;
            unmatched44 = false;
            RAST._IMod _1046_mm;
            RAST._IMod _out16;
            _out16 = (this).GenModule(_1045_m, containingPath);
            _1046_mm = _out16;
            _1044_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1046_mm));
          }
        }
        if (unmatched44) {
          if (_source44.is_Class) {
            DAST._IClass _1047_c = _source44.dtor_Class_a0;
            unmatched44 = false;
            Dafny.ISequence<RAST._IModDecl> _out17;
            _out17 = (this).GenClass(_1047_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1047_c).dtor_name)));
            _1044_generated = _out17;
          }
        }
        if (unmatched44) {
          if (_source44.is_Trait) {
            DAST._ITrait _1048_t = _source44.dtor_Trait_a0;
            unmatched44 = false;
            Dafny.ISequence<Dafny.Rune> _1049_tt;
            Dafny.ISequence<Dafny.Rune> _out18;
            _out18 = (this).GenTrait(_1048_t, containingPath);
            _1049_tt = _out18;
            _1044_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_RawDecl(_1049_tt));
          }
        }
        if (unmatched44) {
          if (_source44.is_Newtype) {
            DAST._INewtype _1050_n = _source44.dtor_Newtype_a0;
            unmatched44 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenNewtype(_1050_n);
            _1044_generated = _out19;
          }
        }
        if (unmatched44) {
          if (_source44.is_SynonymType) {
            DAST._ISynonymType _1051_s = _source44.dtor_SynonymType_a0;
            unmatched44 = false;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenSynonymType(_1051_s);
            _1044_generated = _out20;
          }
        }
        if (unmatched44) {
          DAST._IDatatype _1052_d = _source44.dtor_Datatype_a0;
          unmatched44 = false;
          Dafny.ISequence<RAST._IModDecl> _out21;
          _out21 = (this).GenDatatype(_1052_d);
          _1044_generated = _out21;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1044_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1053_genTpConstraint;
      _1053_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1053_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1053_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1053_genTpConstraint);
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
        for (BigInteger _1054_tpI = BigInteger.Zero; _1054_tpI < _hi6; _1054_tpI++) {
          DAST._ITypeArgDecl _1055_tp;
          _1055_tp = (@params).Select(_1054_tpI);
          DAST._IType _1056_typeArg;
          RAST._ITypeParamDecl _1057_typeParam;
          DAST._IType _out22;
          RAST._ITypeParamDecl _out23;
          (this).GenTypeParam(_1055_tp, out _out22, out _out23);
          _1056_typeArg = _out22;
          _1057_typeParam = _out23;
          RAST._IType _1058_rType;
          RAST._IType _out24;
          _out24 = (this).GenType(_1056_typeArg, false, false);
          _1058_rType = _out24;
          typeParamsSet = Dafny.Set<DAST._IType>.Union(typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1056_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1058_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1057_typeParam));
        }
      }
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1059_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1060_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1061_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1062_whereConstraints;
      Dafny.ISet<DAST._IType> _out25;
      Dafny.ISequence<RAST._IType> _out26;
      Dafny.ISequence<RAST._ITypeParamDecl> _out27;
      Dafny.ISequence<Dafny.Rune> _out28;
      (this).GenTypeParameters((c).dtor_typeParams, out _out25, out _out26, out _out27, out _out28);
      _1059_typeParamsSet = _out25;
      _1060_rTypeParams = _out26;
      _1061_rTypeParamsDecls = _out27;
      _1062_whereConstraints = _out28;
      Dafny.ISequence<Dafny.Rune> _1063_constrainedTypeParams;
      _1063_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1061_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1064_fields;
      _1064_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1065_fieldInits;
      _1065_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1066_fieldI = BigInteger.Zero; _1066_fieldI < _hi7; _1066_fieldI++) {
        DAST._IField _1067_field;
        _1067_field = ((c).dtor_fields).Select(_1066_fieldI);
        RAST._IType _1068_fieldType;
        RAST._IType _out29;
        _out29 = (this).GenType(((_1067_field).dtor_formal).dtor_typ, false, false);
        _1068_fieldType = _out29;
        Dafny.ISequence<Dafny.Rune> _1069_fieldRustName;
        _1069_fieldRustName = DCOMP.__default.escapeName(((_1067_field).dtor_formal).dtor_name);
        _1064_fields = Dafny.Sequence<RAST._IField>.Concat(_1064_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1069_fieldRustName, _1068_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source45 = (_1067_field).dtor_defaultValue;
        bool unmatched45 = true;
        if (unmatched45) {
          if (_source45.is_Some) {
            DAST._IExpression _1070_e = _source45.dtor_value;
            unmatched45 = false;
            {
              RAST._IExpr _1071_expr;
              DCOMP._IOwnership _1072___v42;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1073___v43;
              RAST._IExpr _out30;
              DCOMP._IOwnership _out31;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
              (this).GenExpr(_1070_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
              _1071_expr = _out30;
              _1072___v42 = _out31;
              _1073___v43 = _out32;
              _1065_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1065_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1067_field).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cell::RefCell::new("), (_1071_expr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))))));
            }
          }
        }
        if (unmatched45) {
          unmatched45 = false;
          {
            RAST._IExpr _1074_default;
            _1074_default = RAST.__default.std__Default__default;
            _1065_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1065_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1069_fieldRustName, _1074_default)));
          }
        }
      }
      BigInteger _hi8 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1075_typeParamI = BigInteger.Zero; _1075_typeParamI < _hi8; _1075_typeParamI++) {
        DAST._IType _1076_typeArg;
        RAST._ITypeParamDecl _1077_typeParam;
        DAST._IType _out33;
        RAST._ITypeParamDecl _out34;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1075_typeParamI), out _out33, out _out34);
        _1076_typeArg = _out33;
        _1077_typeParam = _out34;
        RAST._IType _1078_rTypeArg;
        RAST._IType _out35;
        _out35 = (this).GenType(_1076_typeArg, false, false);
        _1078_rTypeArg = _out35;
        _1064_fields = Dafny.Sequence<RAST._IField>.Concat(_1064_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1075_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1078_rTypeArg))))));
        _1065_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1065_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1075_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      Dafny.ISequence<Dafny.Rune> _1079_datatypeName;
      _1079_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IStruct _1080_struct;
      _1080_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1079_datatypeName, _1061_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1064_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1080_struct));
      Dafny.ISequence<RAST._IImplMember> _1081_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1082_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out36;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out37;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(path, (c).dtor_attributes))), _1059_typeParamsSet, out _out36, out _out37);
      _1081_implBodyRaw = _out36;
      _1082_traitBodies = _out37;
      Dafny.ISequence<RAST._IImplMember> _1083_implBody;
      _1083_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(RAST.Expr.create_Identifier(_1079_datatypeName), _1065_fieldInits))))), _1081_implBodyRaw);
      RAST._IImpl _1084_i;
      _1084_i = RAST.Impl.create_Impl(_1061_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1079_datatypeName), _1060_rTypeParams), _1062_whereConstraints, _1083_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1084_i)));
      if ((new BigInteger(((c).dtor_superClasses).Count)).Sign == 1) {
        BigInteger _1085_i;
        _1085_i = BigInteger.Zero;
        while ((_1085_i) < (new BigInteger(((c).dtor_superClasses).Count))) {
          DAST._IType _1086_superClass;
          _1086_superClass = ((c).dtor_superClasses).Select(_1085_i);
          DAST._IType _source46 = _1086_superClass;
          bool unmatched46 = true;
          if (unmatched46) {
            if (_source46.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1087_traitPath = _source46.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _1088_typeArgs = _source46.dtor_typeArgs;
              DAST._IResolvedType resolved0 = _source46.dtor_resolved;
              if (resolved0.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1089___v44 = resolved0.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1090___v45 = resolved0.dtor_attributes;
                unmatched46 = false;
                {
                  RAST._IType _1091_pathStr;
                  RAST._IType _out38;
                  _out38 = DCOMP.COMP.GenPath(_1087_traitPath);
                  _1091_pathStr = _out38;
                  Dafny.ISequence<RAST._IType> _1092_typeArgs;
                  Dafny.ISequence<RAST._IType> _out39;
                  _out39 = (this).GenTypeArgs(_1088_typeArgs, false, false);
                  _1092_typeArgs = _out39;
                  Dafny.ISequence<RAST._IImplMember> _1093_body;
                  _1093_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((_1082_traitBodies).Contains(_1087_traitPath)) {
                    _1093_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1082_traitBodies,_1087_traitPath);
                  }
                  RAST._IType _1094_genSelfPath;
                  RAST._IType _out40;
                  _out40 = DCOMP.COMP.GenPath(path);
                  _1094_genSelfPath = _out40;
                  RAST._IModDecl _1095_x;
                  _1095_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1061_rTypeParamsDecls, RAST.Type.create_TypeApp(_1091_pathStr, _1092_typeArgs), RAST.__default.Rc(RAST.Type.create_TypeApp(_1094_genSelfPath, _1060_rTypeParams)), _1062_whereConstraints, _1093_body));
                  s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1095_x));
                }
              }
            }
          }
          if (unmatched46) {
            DAST._IType _1096___v46 = _source46;
            unmatched46 = false;
          }
          _1085_i = (_1085_i) + (BigInteger.One);
        }
      }
      RAST._IImpl _1097_d;
      _1097_d = RAST.Impl.create_ImplFor(_1061_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1079_datatypeName), _1060_rTypeParams), _1062_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(_1079_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new()"))))))));
      Dafny.ISequence<RAST._IModDecl> _1098_defaultImpl;
      _1098_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1097_d));
      RAST._IImpl _1099_p;
      _1099_p = RAST.Impl.create_ImplFor(_1061_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1079_datatypeName), _1060_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), DCOMP.__default.escapeName(((c).dtor_enclosingModule))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")"))))))));
      Dafny.ISequence<RAST._IModDecl> _1100_printImpl;
      _1100_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1099_p));
      RAST._IImpl _1101_pp;
      _1101_pp = RAST.Impl.create_ImplFor(_1061_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cmp::PartialEq")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1079_datatypeName), _1060_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("eq"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.__default.SelfBorrowed)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ptr::eq(self, other)")))))));
      Dafny.ISequence<RAST._IModDecl> _1102_ptrPartialEqImpl;
      _1102_ptrPartialEqImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1101_pp));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(s, _1098_defaultImpl), _1100_printImpl), _1102_ptrPartialEqImpl);
      return s;
    }
    public Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _1103_typeParamsSet;
      _1103_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1104_typeParamDecls;
      _1104_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1105_typeParams;
      _1105_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1106_tpI;
      _1106_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        while ((_1106_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._ITypeArgDecl _1107_tp;
          _1107_tp = ((t).dtor_typeParams).Select(_1106_tpI);
          DAST._IType _1108_typeArg;
          RAST._ITypeParamDecl _1109_typeParamDecl;
          DAST._IType _out41;
          RAST._ITypeParamDecl _out42;
          (this).GenTypeParam(_1107_tp, out _out41, out _out42);
          _1108_typeArg = _out41;
          _1109_typeParamDecl = _out42;
          _1103_typeParamsSet = Dafny.Set<DAST._IType>.Union(_1103_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1108_typeArg));
          _1104_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1104_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1109_typeParamDecl));
          RAST._IType _1110_typeParam;
          RAST._IType _out43;
          _out43 = (this).GenType(_1108_typeArg, false, false);
          _1110_typeParam = _out43;
          _1105_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1105_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1110_typeParam));
          _1106_tpI = (_1106_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1111_fullPath;
      _1111_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1112_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1113___v47;
      Dafny.ISequence<RAST._IImplMember> _out44;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out45;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_1111_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_1111_fullPath, (t).dtor_attributes)), _1103_typeParamsSet, out _out44, out _out45);
      _1112_implBody = _out44;
      _1113___v47 = _out45;
      s = (RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1104_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1105_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1112_implBody)))._ToString(DCOMP.__default.IND);
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1114_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1115_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1116_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1117_whereConstraints;
      Dafny.ISet<DAST._IType> _out46;
      Dafny.ISequence<RAST._IType> _out47;
      Dafny.ISequence<RAST._ITypeParamDecl> _out48;
      Dafny.ISequence<Dafny.Rune> _out49;
      (this).GenTypeParameters((c).dtor_typeParams, out _out46, out _out47, out _out48, out _out49);
      _1114_typeParamsSet = _out46;
      _1115_rTypeParams = _out47;
      _1116_rTypeParamsDecls = _out48;
      _1117_whereConstraints = _out49;
      Dafny.ISequence<Dafny.Rune> _1118_constrainedTypeParams;
      _1118_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1116_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1119_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source47 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      bool unmatched47 = true;
      if (unmatched47) {
        if (_source47.is_Some) {
          RAST._IType _1120_v = _source47.dtor_value;
          unmatched47 = false;
          _1119_underlyingType = _1120_v;
        }
      }
      if (unmatched47) {
        unmatched47 = false;
        RAST._IType _out50;
        _out50 = (this).GenType((c).dtor_base, false, false);
        _1119_underlyingType = _out50;
      }
      DAST._IType _1121_resultingType;
      _1121_resultingType = DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Newtype((c).dtor_base, (c).dtor_range, false, (c).dtor_attributes));
      Dafny.ISequence<Dafny.Rune> _1122_datatypeName;
      _1122_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1122_datatypeName, _1116_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1119_underlyingType))))));
      RAST._IExpr _1123_fnBody;
      _1123_fnBody = RAST.Expr.create_Identifier(_1122_datatypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source48 = (c).dtor_witnessExpr;
      bool unmatched48 = true;
      if (unmatched48) {
        if (_source48.is_Some) {
          DAST._IExpression _1124_e = _source48.dtor_value;
          unmatched48 = false;
          {
            DAST._IExpression _1125_e;
            _1125_e = ((object.Equals((c).dtor_base, _1121_resultingType)) ? (_1124_e) : (DAST.Expression.create_Convert(_1124_e, (c).dtor_base, _1121_resultingType)));
            RAST._IExpr _1126_eStr;
            DCOMP._IOwnership _1127___v48;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1128___v49;
            RAST._IExpr _out51;
            DCOMP._IOwnership _out52;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out53;
            (this).GenExpr(_1125_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out51, out _out52, out _out53);
            _1126_eStr = _out51;
            _1127___v48 = _out52;
            _1128___v49 = _out53;
            _1123_fnBody = (_1123_fnBody).Apply1(_1126_eStr);
          }
        }
      }
      if (unmatched48) {
        unmatched48 = false;
        {
          _1123_fnBody = (_1123_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1129_body;
      _1129_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1123_fnBody)));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1116_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1122_datatypeName), _1115_rTypeParams), _1117_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1129_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1116_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1122_datatypeName), _1115_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1116_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1122_datatypeName), _1115_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1119_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1130_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1131_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1132_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1133_whereConstraints;
      Dafny.ISet<DAST._IType> _out54;
      Dafny.ISequence<RAST._IType> _out55;
      Dafny.ISequence<RAST._ITypeParamDecl> _out56;
      Dafny.ISequence<Dafny.Rune> _out57;
      (this).GenTypeParameters((c).dtor_typeParams, out _out54, out _out55, out _out56, out _out57);
      _1130_typeParamsSet = _out54;
      _1131_rTypeParams = _out55;
      _1132_rTypeParamsDecls = _out56;
      _1133_whereConstraints = _out57;
      Dafny.ISequence<Dafny.Rune> _1134_constrainedTypeParams;
      _1134_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1132_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<Dafny.Rune> _1135_synonymTypeName;
      _1135_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _1136_resultingType;
      RAST._IType _out58;
      _out58 = (this).GenType((c).dtor_base, false, false);
      _1136_resultingType = _out58;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1135_synonymTypeName, _1132_rTypeParamsDecls, _1136_resultingType)));
      Std.Wrappers._IOption<DAST._IExpression> _source49 = (c).dtor_witnessExpr;
      bool unmatched49 = true;
      if (unmatched49) {
        if (_source49.is_Some) {
          DAST._IExpression _1137_e = _source49.dtor_value;
          unmatched49 = false;
          {
            RAST._IExpr _1138_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1139___v50;
            DCOMP._IEnvironment _1140_newEnv;
            RAST._IExpr _out59;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out60;
            DCOMP._IEnvironment _out61;
            (this).GenStmts((c).dtor_witnessStmts, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), false, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out59, out _out60, out _out61);
            _1138_rStmts = _out59;
            _1139___v50 = _out60;
            _1140_newEnv = _out61;
            RAST._IExpr _1141_rExpr;
            DCOMP._IOwnership _1142___v51;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1143___v52;
            RAST._IExpr _out62;
            DCOMP._IOwnership _out63;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out64;
            (this).GenExpr(_1137_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), _1140_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out62, out _out63, out _out64);
            _1141_rExpr = _out62;
            _1142___v51 = _out63;
            _1143___v52 = _out64;
            Dafny.ISequence<Dafny.Rune> _1144_constantName;
            _1144_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_1144_constantName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1136_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_1138_rStmts).Then(_1141_rExpr)))))));
          }
        }
      }
      if (unmatched49) {
        unmatched49 = false;
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1145_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1146_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1147_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1148_whereConstraints;
      Dafny.ISet<DAST._IType> _out65;
      Dafny.ISequence<RAST._IType> _out66;
      Dafny.ISequence<RAST._ITypeParamDecl> _out67;
      Dafny.ISequence<Dafny.Rune> _out68;
      (this).GenTypeParameters((c).dtor_typeParams, out _out65, out _out66, out _out67, out _out68);
      _1145_typeParamsSet = _out65;
      _1146_rTypeParams = _out66;
      _1147_rTypeParamsDecls = _out67;
      _1148_whereConstraints = _out68;
      Dafny.ISequence<Dafny.Rune> _1149_datatypeName;
      _1149_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1150_ctors;
      _1150_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      BigInteger _hi9 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1151_i = BigInteger.Zero; _1151_i < _hi9; _1151_i++) {
        DAST._IDatatypeCtor _1152_ctor;
        _1152_ctor = ((c).dtor_ctors).Select(_1151_i);
        Dafny.ISequence<RAST._IField> _1153_ctorArgs;
        _1153_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1154_isNumeric;
        _1154_isNumeric = false;
        BigInteger _hi10 = new BigInteger(((_1152_ctor).dtor_args).Count);
        for (BigInteger _1155_j = BigInteger.Zero; _1155_j < _hi10; _1155_j++) {
          DAST._IDatatypeDtor _1156_dtor;
          _1156_dtor = ((_1152_ctor).dtor_args).Select(_1155_j);
          RAST._IType _1157_formalType;
          RAST._IType _out69;
          _out69 = (this).GenType(((_1156_dtor).dtor_formal).dtor_typ, false, false);
          _1157_formalType = _out69;
          Dafny.ISequence<Dafny.Rune> _1158_formalName;
          _1158_formalName = DCOMP.__default.escapeName(((_1156_dtor).dtor_formal).dtor_name);
          if (((_1155_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1158_formalName))) {
            _1154_isNumeric = true;
          }
          if ((((_1155_j).Sign != 0) && (_1154_isNumeric)) && (!(Std.Strings.__default.OfNat(_1155_j)).Equals(_1158_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1158_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1155_j)));
            _1154_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1153_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1153_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1158_formalName, RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1157_formalType))))));
          } else {
            _1153_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1153_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1158_formalName, _1157_formalType))));
          }
        }
        RAST._IFields _1159_namedFields;
        _1159_namedFields = RAST.Fields.create_NamedFields(_1153_ctorArgs);
        if (_1154_isNumeric) {
          _1159_namedFields = (_1159_namedFields).ToNamelessFields();
        }
        _1150_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1150_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1152_ctor).dtor_name), _1159_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1160_selfPath;
      _1160_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1161_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1162_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out70;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out71;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(_1160_selfPath, (c).dtor_attributes))), _1145_typeParamsSet, out _out70, out _out71);
      _1161_implBodyRaw = _out70;
      _1162_traitBodies = _out71;
      Dafny.ISequence<RAST._IImplMember> _1163_implBody;
      _1163_implBody = _1161_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1164_emittedFields;
      _1164_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi11 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1165_i = BigInteger.Zero; _1165_i < _hi11; _1165_i++) {
        DAST._IDatatypeCtor _1166_ctor;
        _1166_ctor = ((c).dtor_ctors).Select(_1165_i);
        BigInteger _hi12 = new BigInteger(((_1166_ctor).dtor_args).Count);
        for (BigInteger _1167_j = BigInteger.Zero; _1167_j < _hi12; _1167_j++) {
          DAST._IDatatypeDtor _1168_dtor;
          _1168_dtor = ((_1166_ctor).dtor_args).Select(_1167_j);
          Dafny.ISequence<Dafny.Rune> _1169_callName;
          _1169_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1168_dtor).dtor_callName, DCOMP.__default.escapeName(((_1168_dtor).dtor_formal).dtor_name));
          if (!((_1164_emittedFields).Contains(_1169_callName))) {
            _1164_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1164_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1169_callName));
            RAST._IType _1170_formalType;
            RAST._IType _out72;
            _out72 = (this).GenType(((_1168_dtor).dtor_formal).dtor_typ, false, false);
            _1170_formalType = _out72;
            Dafny.ISequence<RAST._IMatchCase> _1171_cases;
            _1171_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1172_k = BigInteger.Zero; _1172_k < _hi13; _1172_k++) {
              DAST._IDatatypeCtor _1173_ctor2;
              _1173_ctor2 = ((c).dtor_ctors).Select(_1172_k);
              Dafny.ISequence<Dafny.Rune> _1174_pattern;
              _1174_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1149_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1173_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1175_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1176_hasMatchingField;
              _1176_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1177_patternInner;
              _1177_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1178_isNumeric;
              _1178_isNumeric = false;
              BigInteger _hi14 = new BigInteger(((_1173_ctor2).dtor_args).Count);
              for (BigInteger _1179_l = BigInteger.Zero; _1179_l < _hi14; _1179_l++) {
                DAST._IDatatypeDtor _1180_dtor2;
                _1180_dtor2 = ((_1173_ctor2).dtor_args).Select(_1179_l);
                Dafny.ISequence<Dafny.Rune> _1181_patternName;
                _1181_patternName = DCOMP.__default.escapeName(((_1180_dtor2).dtor_formal).dtor_name);
                if (((_1179_l).Sign == 0) && ((_1181_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1178_isNumeric = true;
                }
                if (_1178_isNumeric) {
                  _1181_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1180_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1179_l)));
                }
                if (object.Equals(((_1168_dtor).dtor_formal).dtor_name, ((_1180_dtor2).dtor_formal).dtor_name)) {
                  _1176_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1181_patternName);
                }
                _1177_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1177_patternInner, _1181_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1178_isNumeric) {
                _1174_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1174_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1177_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1174_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1174_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1177_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1176_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1175_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1176_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1175_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1176_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1175_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _1182_ctorMatch;
              _1182_ctorMatch = RAST.MatchCase.create(_1174_pattern, RAST.Expr.create_RawExpr(_1175_rhs));
              _1171_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1171_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1182_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1171_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1171_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1149_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _1183_methodBody;
            _1183_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1171_cases);
            _1163_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1163_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1169_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1170_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1183_methodBody)))));
          }
        }
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1184_types;
        _1184_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi15 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1185_typeI = BigInteger.Zero; _1185_typeI < _hi15; _1185_typeI++) {
          DAST._IType _1186_typeArg;
          RAST._ITypeParamDecl _1187_rTypeParamDecl;
          DAST._IType _out73;
          RAST._ITypeParamDecl _out74;
          (this).GenTypeParam(((c).dtor_typeParams).Select(_1185_typeI), out _out73, out _out74);
          _1186_typeArg = _out73;
          _1187_rTypeParamDecl = _out74;
          RAST._IType _1188_rTypeArg;
          RAST._IType _out75;
          _out75 = (this).GenType(_1186_typeArg, false, false);
          _1188_rTypeArg = _out75;
          _1184_types = Dafny.Sequence<RAST._IType>.Concat(_1184_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1188_rTypeArg))));
        }
        _1150_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1150_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1189_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1189_tpe);
})), _1184_types)))));
      }
      Dafny.ISequence<RAST._IModDecl> _1190_enumBody;
      _1190_enumBody = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]")), _1149_datatypeName, _1147_rTypeParamsDecls, _1150_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1147_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1149_datatypeName), _1146_rTypeParams), _1148_whereConstraints, _1163_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1191_printImplBodyCases;
      _1191_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1192_i = BigInteger.Zero; _1192_i < _hi16; _1192_i++) {
        DAST._IDatatypeCtor _1193_ctor;
        _1193_ctor = ((c).dtor_ctors).Select(_1192_i);
        Dafny.ISequence<Dafny.Rune> _1194_ctorMatch;
        _1194_ctorMatch = DCOMP.__default.escapeName((_1193_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1195_modulePrefix;
        _1195_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1196_ctorName;
        _1196_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1195_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1193_ctor).dtor_name));
        if (((new BigInteger((_1196_ctorName).Count)) >= (new BigInteger(13))) && (((_1196_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1196_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1197_printRhs;
        _1197_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1196_ctorName), (((_1193_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        bool _1198_isNumeric;
        _1198_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1199_ctorMatchInner;
        _1199_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi17 = new BigInteger(((_1193_ctor).dtor_args).Count);
        for (BigInteger _1200_j = BigInteger.Zero; _1200_j < _hi17; _1200_j++) {
          DAST._IDatatypeDtor _1201_dtor;
          _1201_dtor = ((_1193_ctor).dtor_args).Select(_1200_j);
          Dafny.ISequence<Dafny.Rune> _1202_patternName;
          _1202_patternName = DCOMP.__default.escapeName(((_1201_dtor).dtor_formal).dtor_name);
          if (((_1200_j).Sign == 0) && ((_1202_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1198_isNumeric = true;
          }
          if (_1198_isNumeric) {
            _1202_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1201_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1200_j)));
          }
          _1199_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1199_ctorMatchInner, _1202_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1200_j).Sign == 1) {
            _1197_printRhs = (_1197_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1197_printRhs = (_1197_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1202_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))));
        }
        if (_1198_isNumeric) {
          _1194_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1194_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1199_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1194_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1194_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1199_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1193_ctor).dtor_hasAnyArgs) {
          _1197_printRhs = (_1197_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1197_printRhs = (_1197_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1191_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1191_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1149_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1194_ctorMatch), RAST.Expr.create_Block(_1197_printRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _1191_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1191_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1149_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1203_defaultConstrainedTypeParams;
      _1203_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1147_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      RAST._IExpr _1204_printImplBody;
      _1204_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1191_printImplBodyCases);
      Dafny.ISequence<RAST._IModDecl> _1205_printImpl;
      _1205_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1147_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1149_datatypeName), _1146_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1147_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1149_datatypeName), _1146_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1204_printImplBody)))))));
      Dafny.ISequence<RAST._IModDecl> _1206_defaultImpl;
      _1206_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      Dafny.ISequence<RAST._IModDecl> _1207_asRefImpl;
      _1207_asRefImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1208_structName;
        _1208_structName = (RAST.Expr.create_Identifier(_1149_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1209_structAssignments;
        _1209_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi18 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1210_i = BigInteger.Zero; _1210_i < _hi18; _1210_i++) {
          DAST._IDatatypeDtor _1211_dtor;
          _1211_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1210_i);
          _1209_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1209_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1211_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1212_defaultConstrainedTypeParams;
        _1212_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1147_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1213_fullType;
        _1213_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1149_datatypeName), _1146_rTypeParams);
        _1206_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1212_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1213_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1213_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1208_structName, _1209_structAssignments))))))));
        _1207_asRefImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1147_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_1213_fullType), RAST.Type.create_Borrowed(_1213_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self)))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(_1190_enumBody, _1205_printImpl), _1206_defaultImpl), _1207_asRefImpl);
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
        for (BigInteger _1214_i = BigInteger.Zero; _1214_i < _hi19; _1214_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1214_i))));
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
        for (BigInteger _1215_i = BigInteger.Zero; _1215_i < _hi20; _1215_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1215_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding, bool inFn)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger((args).Count)).Sign == 1) {
        BigInteger _1216_i;
        _1216_i = BigInteger.Zero;
        while ((_1216_i) < (new BigInteger((args).Count))) {
          RAST._IType _1217_genTp;
          RAST._IType _out76;
          _out76 = (this).GenType((args).Select(_1216_i), inBinding, inFn);
          _1217_genTp = _out76;
          s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1217_genTp));
          _1216_i = (_1216_i) + (BigInteger.One);
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
      DAST._IType _source50 = c;
      bool unmatched50 = true;
      if (unmatched50) {
        if (_source50.is_Path) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1218_p = _source50.dtor_Path_a0;
          Dafny.ISequence<DAST._IType> _1219_args = _source50.dtor_typeArgs;
          DAST._IResolvedType _1220_resolved = _source50.dtor_resolved;
          unmatched50 = false;
          {
            RAST._IType _1221_t;
            RAST._IType _out77;
            _out77 = DCOMP.COMP.GenPath(_1218_p);
            _1221_t = _out77;
            Dafny.ISequence<RAST._IType> _1222_typeArgs;
            Dafny.ISequence<RAST._IType> _out78;
            _out78 = (this).GenTypeArgs(_1219_args, inBinding, inFn);
            _1222_typeArgs = _out78;
            s = RAST.Type.create_TypeApp(_1221_t, _1222_typeArgs);
            DAST._IResolvedType _source51 = _1220_resolved;
            bool unmatched51 = true;
            if (unmatched51) {
              if (_source51.is_Datatype) {
                DAST._IDatatypeType datatypeType0 = _source51.dtor_datatypeType;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1223___v53 = datatypeType0.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1224_attributes = datatypeType0.dtor_attributes;
                unmatched51 = false;
                {
                  if ((this).IsRcWrapped(_1224_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched51) {
              if (_source51.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1225___v54 = _source51.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1226___v55 = _source51.dtor_attributes;
                unmatched51 = false;
                {
                  if ((_1218_p).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
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
            if (unmatched51) {
              DAST._IType _1227_t = _source51.dtor_baseType;
              DAST._INewtypeRange _1228_range = _source51.dtor_range;
              bool _1229_erased = _source51.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1230_attributes = _source51.dtor_attributes;
              unmatched51 = false;
              {
                if (_1229_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source52 = DCOMP.COMP.NewtypeToRustType(_1227_t, _1228_range);
                  bool unmatched52 = true;
                  if (unmatched52) {
                    if (_source52.is_Some) {
                      RAST._IType _1231_v = _source52.dtor_value;
                      unmatched52 = false;
                      s = _1231_v;
                    }
                  }
                  if (unmatched52) {
                    unmatched52 = false;
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched50) {
        if (_source50.is_Nullable) {
          DAST._IType _1232_inner = _source50.dtor_Nullable_a0;
          unmatched50 = false;
          {
            RAST._IType _1233_innerExpr;
            RAST._IType _out79;
            _out79 = (this).GenType(_1232_inner, inBinding, inFn);
            _1233_innerExpr = _out79;
            s = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::option::Option")), Dafny.Sequence<RAST._IType>.FromElements(_1233_innerExpr));
          }
        }
      }
      if (unmatched50) {
        if (_source50.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1234_types = _source50.dtor_Tuple_a0;
          unmatched50 = false;
          {
            Dafny.ISequence<RAST._IType> _1235_args;
            _1235_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1236_i;
            _1236_i = BigInteger.Zero;
            while ((_1236_i) < (new BigInteger((_1234_types).Count))) {
              RAST._IType _1237_generated;
              RAST._IType _out80;
              _out80 = (this).GenType((_1234_types).Select(_1236_i), inBinding, inFn);
              _1237_generated = _out80;
              _1235_args = Dafny.Sequence<RAST._IType>.Concat(_1235_args, Dafny.Sequence<RAST._IType>.FromElements(_1237_generated));
              _1236_i = (_1236_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1234_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1235_args)) : (RAST.__default.SystemTupleType(_1235_args)));
          }
        }
      }
      if (unmatched50) {
        if (_source50.is_Array) {
          DAST._IType _1238_element = _source50.dtor_element;
          BigInteger _1239_dims = _source50.dtor_dims;
          unmatched50 = false;
          {
            RAST._IType _1240_elem;
            RAST._IType _out81;
            _out81 = (this).GenType(_1238_element, inBinding, inFn);
            _1240_elem = _out81;
            s = _1240_elem;
            BigInteger _1241_i;
            _1241_i = BigInteger.Zero;
            while ((_1241_i) < (_1239_dims)) {
              s = RAST.__default.Rc(RAST.__default.RefCell(RAST.__default.Vec(s)));
              _1241_i = (_1241_i) + (BigInteger.One);
            }
          }
        }
      }
      if (unmatched50) {
        if (_source50.is_Seq) {
          DAST._IType _1242_element = _source50.dtor_element;
          unmatched50 = false;
          {
            RAST._IType _1243_elem;
            RAST._IType _out82;
            _out82 = (this).GenType(_1242_element, inBinding, inFn);
            _1243_elem = _out82;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1243_elem));
          }
        }
      }
      if (unmatched50) {
        if (_source50.is_Set) {
          DAST._IType _1244_element = _source50.dtor_element;
          unmatched50 = false;
          {
            RAST._IType _1245_elem;
            RAST._IType _out83;
            _out83 = (this).GenType(_1244_element, inBinding, inFn);
            _1245_elem = _out83;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1245_elem));
          }
        }
      }
      if (unmatched50) {
        if (_source50.is_Multiset) {
          DAST._IType _1246_element = _source50.dtor_element;
          unmatched50 = false;
          {
            RAST._IType _1247_elem;
            RAST._IType _out84;
            _out84 = (this).GenType(_1246_element, inBinding, inFn);
            _1247_elem = _out84;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1247_elem));
          }
        }
      }
      if (unmatched50) {
        if (_source50.is_Map) {
          DAST._IType _1248_key = _source50.dtor_key;
          DAST._IType _1249_value = _source50.dtor_value;
          unmatched50 = false;
          {
            RAST._IType _1250_keyType;
            RAST._IType _out85;
            _out85 = (this).GenType(_1248_key, inBinding, inFn);
            _1250_keyType = _out85;
            RAST._IType _1251_valueType;
            RAST._IType _out86;
            _out86 = (this).GenType(_1249_value, inBinding, inFn);
            _1251_valueType = _out86;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1250_keyType, _1251_valueType));
          }
        }
      }
      if (unmatched50) {
        if (_source50.is_MapBuilder) {
          DAST._IType _1252_key = _source50.dtor_key;
          DAST._IType _1253_value = _source50.dtor_value;
          unmatched50 = false;
          {
            RAST._IType _1254_keyType;
            RAST._IType _out87;
            _out87 = (this).GenType(_1252_key, inBinding, inFn);
            _1254_keyType = _out87;
            RAST._IType _1255_valueType;
            RAST._IType _out88;
            _out88 = (this).GenType(_1253_value, inBinding, inFn);
            _1255_valueType = _out88;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1254_keyType, _1255_valueType));
          }
        }
      }
      if (unmatched50) {
        if (_source50.is_SetBuilder) {
          DAST._IType _1256_elem = _source50.dtor_element;
          unmatched50 = false;
          {
            RAST._IType _1257_elemType;
            RAST._IType _out89;
            _out89 = (this).GenType(_1256_elem, inBinding, inFn);
            _1257_elemType = _out89;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1257_elemType));
          }
        }
      }
      if (unmatched50) {
        if (_source50.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1258_args = _source50.dtor_args;
          DAST._IType _1259_result = _source50.dtor_result;
          unmatched50 = false;
          {
            Dafny.ISequence<RAST._IType> _1260_argTypes;
            _1260_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1261_i;
            _1261_i = BigInteger.Zero;
            while ((_1261_i) < (new BigInteger((_1258_args).Count))) {
              RAST._IType _1262_generated;
              RAST._IType _out90;
              _out90 = (this).GenType((_1258_args).Select(_1261_i), inBinding, true);
              _1262_generated = _out90;
              _1260_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1260_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1262_generated)));
              _1261_i = (_1261_i) + (BigInteger.One);
            }
            RAST._IType _1263_resultType;
            RAST._IType _out91;
            _out91 = (this).GenType(_1259_result, inBinding, (inFn) || (inBinding));
            _1263_resultType = _out91;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1260_argTypes, _1263_resultType)));
          }
        }
      }
      if (unmatched50) {
        if (_source50.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h110 = _source50.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1264_name = _h110;
          unmatched50 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1264_name));
        }
      }
      if (unmatched50) {
        if (_source50.is_Primitive) {
          DAST._IPrimitive _1265_p = _source50.dtor_Primitive_a0;
          unmatched50 = false;
          {
            DAST._IPrimitive _source53 = _1265_p;
            bool unmatched53 = true;
            if (unmatched53) {
              if (_source53.is_Int) {
                unmatched53 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
              }
            }
            if (unmatched53) {
              if (_source53.is_Real) {
                unmatched53 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
              }
            }
            if (unmatched53) {
              if (_source53.is_String) {
                unmatched53 = false;
                s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
              }
            }
            if (unmatched53) {
              if (_source53.is_Bool) {
                unmatched53 = false;
                s = RAST.Type.create_Bool();
              }
            }
            if (unmatched53) {
              unmatched53 = false;
              s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
            }
          }
        }
      }
      if (unmatched50) {
        Dafny.ISequence<Dafny.Rune> _1266_v = _source50.dtor_Passthrough_a0;
        unmatched50 = false;
        s = RAST.__default.RawType(_1266_v);
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
      for (BigInteger _1267_i = BigInteger.Zero; _1267_i < _hi21; _1267_i++) {
        DAST._IMethod _source54 = (body).Select(_1267_i);
        bool unmatched54 = true;
        if (unmatched54) {
          DAST._IMethod _1268_m = _source54;
          unmatched54 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source55 = (_1268_m).dtor_overridingPath;
            bool unmatched55 = true;
            if (unmatched55) {
              if (_source55.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1269_p = _source55.dtor_value;
                unmatched55 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1270_existing;
                  _1270_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1269_p)) {
                    _1270_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1269_p);
                  }
                  RAST._IImplMember _1271_genMethod;
                  RAST._IImplMember _out92;
                  _out92 = (this).GenMethod(_1268_m, true, enclosingType, enclosingTypeParams);
                  _1271_genMethod = _out92;
                  _1270_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1270_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1271_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1269_p, _1270_existing)));
                }
              }
            }
            if (unmatched55) {
              unmatched55 = false;
              {
                RAST._IImplMember _1272_generated;
                RAST._IImplMember _out93;
                _out93 = (this).GenMethod(_1268_m, forTrait, enclosingType, enclosingTypeParams);
                _1272_generated = _out93;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1272_generated));
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
      for (BigInteger _1273_i = BigInteger.Zero; _1273_i < _hi22; _1273_i++) {
        DAST._IFormal _1274_param;
        _1274_param = (@params).Select(_1273_i);
        RAST._IType _1275_paramType;
        RAST._IType _out94;
        _out94 = (this).GenType((_1274_param).dtor_typ, false, false);
        _1275_paramType = _out94;
        if ((!((_1275_paramType).CanReadWithoutClone())) && (!((_1274_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1275_paramType = RAST.Type.create_Borrowed(_1275_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_1274_param).dtor_name), _1275_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1276_params;
      Dafny.ISequence<RAST._IFormal> _out95;
      _out95 = (this).GenParams((m).dtor_params);
      _1276_params = _out95;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1277_paramNames;
      _1277_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1278_paramTypes;
      _1278_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi23 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1279_paramI = BigInteger.Zero; _1279_paramI < _hi23; _1279_paramI++) {
        DAST._IFormal _1280_dafny__formal;
        _1280_dafny__formal = ((m).dtor_params).Select(_1279_paramI);
        RAST._IFormal _1281_formal;
        _1281_formal = (_1276_params).Select(_1279_paramI);
        Dafny.ISequence<Dafny.Rune> _1282_name;
        _1282_name = (_1281_formal).dtor_name;
        _1277_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1277_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1282_name));
        _1278_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1278_paramTypes, _1282_name, (_1281_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1283_fnName;
      _1283_fnName = DCOMP.__default.escapeName((m).dtor_name);
      Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1284_selfIdentifier;
      _1284_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1285_selfId;
        _1285_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((_1283_fnName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_ctor"))) {
          _1285_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        if (forTrait) {
          RAST._IFormal _1286_selfFormal;
          _1286_selfFormal = RAST.Formal.selfBorrowedMut;
          _1276_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1286_selfFormal), _1276_params);
        } else {
          RAST._IType _1287_tpe;
          RAST._IType _out96;
          _out96 = (this).GenType(enclosingType, false, false);
          _1287_tpe = _out96;
          if (!((_1287_tpe).CanReadWithoutClone())) {
            _1287_tpe = RAST.Type.create_Borrowed(_1287_tpe);
          }
          _1276_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1285_selfId, _1287_tpe)), _1276_params);
        }
        _1284_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1285_selfId);
      }
      Dafny.ISequence<RAST._IType> _1288_retTypeArgs;
      _1288_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1289_typeI;
      _1289_typeI = BigInteger.Zero;
      while ((_1289_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1290_typeExpr;
        RAST._IType _out97;
        _out97 = (this).GenType(((m).dtor_outTypes).Select(_1289_typeI), false, false);
        _1290_typeExpr = _out97;
        _1288_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1288_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1290_typeExpr));
        _1289_typeI = (_1289_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1291_visibility;
      _1291_visibility = RAST.Visibility.create_PUB();
      Dafny.ISequence<DAST._ITypeArgDecl> _1292_typeParamsFiltered;
      _1292_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi24 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1293_typeParamI = BigInteger.Zero; _1293_typeParamI < _hi24; _1293_typeParamI++) {
        DAST._ITypeArgDecl _1294_typeParam;
        _1294_typeParam = ((m).dtor_typeParams).Select(_1293_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1294_typeParam).dtor_name)))) {
          _1292_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1292_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1294_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1295_typeParams;
      _1295_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1292_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi25 = new BigInteger((_1292_typeParamsFiltered).Count);
        for (BigInteger _1296_i = BigInteger.Zero; _1296_i < _hi25; _1296_i++) {
          DAST._IType _1297_typeArg;
          RAST._ITypeParamDecl _1298_rTypeParamDecl;
          DAST._IType _out98;
          RAST._ITypeParamDecl _out99;
          (this).GenTypeParam((_1292_typeParamsFiltered).Select(_1296_i), out _out98, out _out99);
          _1297_typeArg = _out98;
          _1298_rTypeParamDecl = _out99;
          var _pat_let_tv101 = _1298_rTypeParamDecl;
          _1298_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1298_rTypeParamDecl, _pat_let6_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let6_0, _1299_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Dafny.Sequence<RAST._IType>.Concat((_pat_let_tv101).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default")))), _pat_let7_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let7_0, _1300_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1299_dt__update__tmp_h0).dtor_content, _1300_dt__update_hconstraints_h0)))));
          _1295_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1295_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1298_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1301_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1302_env = DCOMP.Environment.Default();
      RAST._IExpr _1303_preBody;
      _1303_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      if ((m).dtor_hasBody) {
        RAST._IExpr _1304_earlyReturn;
        _1304_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source56 = (m).dtor_outVars;
        bool unmatched56 = true;
        if (unmatched56) {
          if (_source56.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1305_outVars = _source56.dtor_value;
            unmatched56 = false;
            {
              Dafny.ISequence<RAST._IExpr> _1306_tupleArgs;
              _1306_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi26 = new BigInteger((_1305_outVars).Count);
              for (BigInteger _1307_outI = BigInteger.Zero; _1307_outI < _hi26; _1307_outI++) {
                Dafny.ISequence<Dafny.Rune> _1308_outVar;
                _1308_outVar = (_1305_outVars).Select(_1307_outI);
                RAST._IType _1309_outType;
                RAST._IType _out100;
                _out100 = (this).GenType(((m).dtor_outTypes).Select(_1307_outI), false, false);
                _1309_outType = _out100;
                Dafny.ISequence<Dafny.Rune> _1310_outName;
                _1310_outName = DCOMP.__default.escapeName((_1308_outVar));
                _1277_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1277_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1310_outName));
                RAST._IType _1311_outMaybeType;
                _1311_outMaybeType = (((_1309_outType).CanReadWithoutClone()) ? (_1309_outType) : (RAST.Type.create_Borrowed(_1309_outType)));
                _1278_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1278_paramTypes, _1310_outName, _1311_outMaybeType);
                RAST._IExpr _1312_outVarReturn;
                DCOMP._IOwnership _1313___v56;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1314___v57;
                RAST._IExpr _out101;
                DCOMP._IOwnership _out102;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out103;
                (this).GenExpr(DAST.Expression.create_Ident((_1308_outVar)), Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1310_outName), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>, RAST._IType>(_1310_outName, _1311_outMaybeType))), DCOMP.Ownership.create_OwnershipOwned(), out _out101, out _out102, out _out103);
                _1312_outVarReturn = _out101;
                _1313___v56 = _out102;
                _1314___v57 = _out103;
                _1306_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1306_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1312_outVarReturn));
              }
              if ((new BigInteger((_1306_tupleArgs).Count)) == (BigInteger.One)) {
                _1304_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1306_tupleArgs).Select(BigInteger.Zero)));
              } else {
                _1304_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1306_tupleArgs)));
              }
            }
          }
        }
        if (unmatched56) {
          unmatched56 = false;
        }
        _1302_env = DCOMP.Environment.create(_1277_paramNames, _1278_paramTypes);
        RAST._IExpr _1315_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1316___v58;
        DCOMP._IEnvironment _1317___v59;
        RAST._IExpr _out104;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out105;
        DCOMP._IEnvironment _out106;
        (this).GenStmts((m).dtor_body, _1284_selfIdentifier, _1302_env, true, _1304_earlyReturn, out _out104, out _out105, out _out106);
        _1315_body = _out104;
        _1316___v58 = _out105;
        _1317___v59 = _out106;
        _1301_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1303_preBody).Then(_1315_body));
      } else {
        _1302_env = DCOMP.Environment.create(_1277_paramNames, _1278_paramTypes);
        _1301_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1291_visibility, RAST.Fn.create(_1283_fnName, _1295_typeParams, _1276_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1288_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1288_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1288_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1301_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1318_declarations;
      _1318_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1319_i;
      _1319_i = BigInteger.Zero;
      newEnv = env;
      while ((_1319_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _1320_stmt;
        _1320_stmt = (stmts).Select(_1319_i);
        RAST._IExpr _1321_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1322_recIdents;
        DCOMP._IEnvironment _1323_newEnv2;
        RAST._IExpr _out107;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out108;
        DCOMP._IEnvironment _out109;
        (this).GenStmt(_1320_stmt, selfIdent, newEnv, (isLast) && ((_1319_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out107, out _out108, out _out109);
        _1321_stmtExpr = _out107;
        _1322_recIdents = _out108;
        _1323_newEnv2 = _out109;
        newEnv = _1323_newEnv2;
        DAST._IStatement _source57 = _1320_stmt;
        bool unmatched57 = true;
        if (unmatched57) {
          if (_source57.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1324_name = _source57.dtor_name;
            DAST._IType _1325___v60 = _source57.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> _1326___v61 = _source57.dtor_maybeValue;
            unmatched57 = false;
            {
              _1318_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1318_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_1324_name)));
            }
          }
        }
        if (unmatched57) {
          DAST._IStatement _1327___v62 = _source57;
          unmatched57 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1322_recIdents, _1318_declarations));
        generated = (generated).Then(_1321_stmtExpr);
        _1319_i = (_1319_i) + (BigInteger.One);
      }
    }
    public void GenAssignLhs(DAST._IAssignLhs lhs, RAST._IExpr rhs, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, out RAST._IExpr generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      newEnv = env;
      DAST._IAssignLhs _source58 = lhs;
      bool unmatched58 = true;
      if (unmatched58) {
        if (_source58.is_Ident) {
          Dafny.ISequence<Dafny.Rune> ident0 = _source58.dtor_ident;
          Dafny.ISequence<Dafny.Rune> _1328_id = ident0;
          unmatched58 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1329_idRust;
            _1329_idRust = DCOMP.__default.escapeName(_1328_id);
            if (((env).IsBorrowed(_1329_idRust)) || ((env).IsBorrowedMut(_1329_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1329_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1329_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1329_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Select) {
          DAST._IExpression _1330_on = _source58.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1331_field = _source58.dtor_field;
          unmatched58 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1332_fieldName;
            _1332_fieldName = DCOMP.__default.escapeName(_1331_field);
            RAST._IExpr _1333_onExpr;
            DCOMP._IOwnership _1334_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1335_recIdents;
            RAST._IExpr _out110;
            DCOMP._IOwnership _out111;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out112;
            (this).GenExpr(_1330_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out110, out _out111, out _out112);
            _1333_onExpr = _out110;
            _1334_onOwned = _out111;
            _1335_recIdents = _out112;
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*("), (_1333_onExpr)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _1332_fieldName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()) = ")), (rhs)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";")));
            readIdents = _1335_recIdents;
            needsIIFE = true;
          }
        }
      }
      if (unmatched58) {
        DAST._IExpression _1336_on = _source58.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1337_indices = _source58.dtor_indices;
        unmatched58 = false;
        {
          RAST._IExpr _1338_onExpr;
          DCOMP._IOwnership _1339_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1340_recIdents;
          RAST._IExpr _out113;
          DCOMP._IOwnership _out114;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out115;
          (this).GenExpr(_1336_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out113, out _out114, out _out115);
          _1338_onExpr = _out113;
          _1339_onOwned = _out114;
          _1340_recIdents = _out115;
          readIdents = _1340_recIdents;
          Dafny.ISequence<Dafny.Rune> _1341_r;
          _1341_r = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          BigInteger _1342_i;
          _1342_i = BigInteger.Zero;
          while ((_1342_i) < (new BigInteger((_1337_indices).Count))) {
            RAST._IExpr _1343_idx;
            DCOMP._IOwnership _1344___v63;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1345_recIdentsIdx;
            RAST._IExpr _out116;
            DCOMP._IOwnership _out117;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out118;
            (this).GenExpr((_1337_indices).Select(_1342_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out116, out _out117, out _out118);
            _1343_idx = _out116;
            _1344___v63 = _out117;
            _1345_recIdentsIdx = _out118;
            _1341_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1341_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let __idx")), Std.Strings.__default.OfNat(_1342_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = <usize as ::dafny_runtime::NumCast>::from(")), (_1343_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap();\n"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1345_recIdentsIdx);
            _1342_i = (_1342_i) + (BigInteger.One);
          }
          _1341_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1341_r, (_1338_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()"));
          _1342_i = BigInteger.Zero;
          while ((_1342_i) < (new BigInteger((_1337_indices).Count))) {
            _1341_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1341_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[__idx")), Std.Strings.__default.OfNat(_1342_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
            _1342_i = (_1342_i) + (BigInteger.One);
          }
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1341_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), (rhs)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n}")));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source59 = stmt;
      bool unmatched59 = true;
      if (unmatched59) {
        if (_source59.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1346_name = _source59.dtor_name;
          DAST._IType _1347_typ = _source59.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source59.dtor_maybeValue;
          if (maybeValue0.is_Some) {
            DAST._IExpression _1348_expression = maybeValue0.dtor_value;
            unmatched59 = false;
            {
              RAST._IType _1349_tpe;
              RAST._IType _out119;
              _out119 = (this).GenType(_1347_typ, true, false);
              _1349_tpe = _out119;
              RAST._IExpr _1350_expr;
              DCOMP._IOwnership _1351_exprOwnership;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1352_recIdents;
              RAST._IExpr _out120;
              DCOMP._IOwnership _out121;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out122;
              (this).GenExpr(_1348_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out120, out _out121, out _out122);
              _1350_expr = _out120;
              _1351_exprOwnership = _out121;
              _1352_recIdents = _out122;
              readIdents = _1352_recIdents;
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_1346_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1349_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1350_expr));
              newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_1346_name), _1349_tpe);
            }
          }
        }
      }
      if (unmatched59) {
        if (_source59.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1353_name = _source59.dtor_name;
          DAST._IType _1354_typ = _source59.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source59.dtor_maybeValue;
          if (maybeValue1.is_None) {
            unmatched59 = false;
            {
              DAST._IStatement _1355_newStmt;
              _1355_newStmt = DAST.Statement.create_DeclareVar(_1353_name, _1354_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1354_typ)));
              RAST._IExpr _out123;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out124;
              DCOMP._IEnvironment _out125;
              (this).GenStmt(_1355_newStmt, selfIdent, env, isLast, earlyReturn, out _out123, out _out124, out _out125);
              generated = _out123;
              readIdents = _out124;
              newEnv = _out125;
            }
          }
        }
      }
      if (unmatched59) {
        if (_source59.is_Assign) {
          DAST._IAssignLhs _1356_lhs = _source59.dtor_lhs;
          DAST._IExpression _1357_expression = _source59.dtor_value;
          unmatched59 = false;
          {
            RAST._IExpr _1358_exprGen;
            DCOMP._IOwnership _1359___v64;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1360_exprIdents;
            RAST._IExpr _out126;
            DCOMP._IOwnership _out127;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out128;
            (this).GenExpr(_1357_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out126, out _out127, out _out128);
            _1358_exprGen = _out126;
            _1359___v64 = _out127;
            _1360_exprIdents = _out128;
            if ((_1356_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1361_rustId;
              _1361_rustId = DCOMP.__default.escapeName(((_1356_lhs).dtor_ident));
              Std.Wrappers._IOption<RAST._IType> _1362_tpe;
              _1362_tpe = (env).GetType(_1361_rustId);
            }
            RAST._IExpr _1363_lhsGen;
            bool _1364_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1365_recIdents;
            DCOMP._IEnvironment _1366_resEnv;
            RAST._IExpr _out129;
            bool _out130;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
            DCOMP._IEnvironment _out132;
            (this).GenAssignLhs(_1356_lhs, _1358_exprGen, selfIdent, env, out _out129, out _out130, out _out131, out _out132);
            _1363_lhsGen = _out129;
            _1364_needsIIFE = _out130;
            _1365_recIdents = _out131;
            _1366_resEnv = _out132;
            generated = _1363_lhsGen;
            newEnv = _1366_resEnv;
            if (_1364_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1365_recIdents, _1360_exprIdents);
          }
        }
      }
      if (unmatched59) {
        if (_source59.is_If) {
          DAST._IExpression _1367_cond = _source59.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1368_thnDafny = _source59.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1369_elsDafny = _source59.dtor_els;
          unmatched59 = false;
          {
            RAST._IExpr _1370_cond;
            DCOMP._IOwnership _1371___v65;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1372_recIdents;
            RAST._IExpr _out133;
            DCOMP._IOwnership _out134;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
            (this).GenExpr(_1367_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out133, out _out134, out _out135);
            _1370_cond = _out133;
            _1371___v65 = _out134;
            _1372_recIdents = _out135;
            Dafny.ISequence<Dafny.Rune> _1373_condString;
            _1373_condString = (_1370_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1372_recIdents;
            RAST._IExpr _1374_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1375_thnIdents;
            DCOMP._IEnvironment _1376_thnEnv;
            RAST._IExpr _out136;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
            DCOMP._IEnvironment _out138;
            (this).GenStmts(_1368_thnDafny, selfIdent, env, isLast, earlyReturn, out _out136, out _out137, out _out138);
            _1374_thn = _out136;
            _1375_thnIdents = _out137;
            _1376_thnEnv = _out138;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1375_thnIdents);
            RAST._IExpr _1377_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1378_elsIdents;
            DCOMP._IEnvironment _1379_elsEnv;
            RAST._IExpr _out139;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out140;
            DCOMP._IEnvironment _out141;
            (this).GenStmts(_1369_elsDafny, selfIdent, env, isLast, earlyReturn, out _out139, out _out140, out _out141);
            _1377_els = _out139;
            _1378_elsIdents = _out140;
            _1379_elsEnv = _out141;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1378_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1370_cond, _1374_thn, _1377_els);
          }
        }
      }
      if (unmatched59) {
        if (_source59.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1380_lbl = _source59.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1381_body = _source59.dtor_body;
          unmatched59 = false;
          {
            RAST._IExpr _1382_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1383_bodyIdents;
            DCOMP._IEnvironment _1384_env2;
            RAST._IExpr _out142;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out143;
            DCOMP._IEnvironment _out144;
            (this).GenStmts(_1381_body, selfIdent, env, isLast, earlyReturn, out _out142, out _out143, out _out144);
            _1382_body = _out142;
            _1383_bodyIdents = _out143;
            _1384_env2 = _out144;
            readIdents = _1383_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1380_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1382_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched59) {
        if (_source59.is_While) {
          DAST._IExpression _1385_cond = _source59.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1386_body = _source59.dtor_body;
          unmatched59 = false;
          {
            RAST._IExpr _1387_cond;
            DCOMP._IOwnership _1388___v66;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1389_recIdents;
            RAST._IExpr _out145;
            DCOMP._IOwnership _out146;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out147;
            (this).GenExpr(_1385_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out145, out _out146, out _out147);
            _1387_cond = _out145;
            _1388___v66 = _out146;
            _1389_recIdents = _out147;
            readIdents = _1389_recIdents;
            RAST._IExpr _1390_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1391_bodyIdents;
            DCOMP._IEnvironment _1392_bodyEnv;
            RAST._IExpr _out148;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out149;
            DCOMP._IEnvironment _out150;
            (this).GenStmts(_1386_body, selfIdent, env, false, earlyReturn, out _out148, out _out149, out _out150);
            _1390_bodyExpr = _out148;
            _1391_bodyIdents = _out149;
            _1392_bodyEnv = _out150;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1391_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1387_cond), _1390_bodyExpr);
          }
        }
      }
      if (unmatched59) {
        if (_source59.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1393_boundName = _source59.dtor_boundName;
          DAST._IType _1394_boundType = _source59.dtor_boundType;
          DAST._IExpression _1395_over = _source59.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1396_body = _source59.dtor_body;
          unmatched59 = false;
          {
            RAST._IExpr _1397_over;
            DCOMP._IOwnership _1398___v67;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1399_recIdents;
            RAST._IExpr _out151;
            DCOMP._IOwnership _out152;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out153;
            (this).GenExpr(_1395_over, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out151, out _out152, out _out153);
            _1397_over = _out151;
            _1398___v67 = _out152;
            _1399_recIdents = _out153;
            RAST._IType _1400_boundTpe;
            RAST._IType _out154;
            _out154 = (this).GenType(_1394_boundType, false, false);
            _1400_boundTpe = _out154;
            readIdents = _1399_recIdents;
            Dafny.ISequence<Dafny.Rune> _1401_boundRName;
            _1401_boundRName = DCOMP.__default.escapeName(_1393_boundName);
            RAST._IExpr _1402_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1403_bodyIdents;
            DCOMP._IEnvironment _1404_bodyEnv;
            RAST._IExpr _out155;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
            DCOMP._IEnvironment _out157;
            (this).GenStmts(_1396_body, selfIdent, (env).AddAssigned(_1401_boundRName, _1400_boundTpe), false, earlyReturn, out _out155, out _out156, out _out157);
            _1402_bodyExpr = _out155;
            _1403_bodyIdents = _out156;
            _1404_bodyEnv = _out157;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1403_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1401_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1401_boundRName, _1397_over, _1402_bodyExpr);
          }
        }
      }
      if (unmatched59) {
        if (_source59.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1405_toLabel = _source59.dtor_toLabel;
          unmatched59 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source60 = _1405_toLabel;
            bool unmatched60 = true;
            if (unmatched60) {
              if (_source60.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1406_lbl = _source60.dtor_value;
                unmatched60 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1406_lbl)));
                }
              }
            }
            if (unmatched60) {
              unmatched60 = false;
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched59) {
        if (_source59.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1407_body = _source59.dtor_body;
          unmatched59 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
            }
            newEnv = env;
            BigInteger _hi27 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1408_paramI = BigInteger.Zero; _1408_paramI < _hi27; _1408_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1409_param;
              _1409_param = ((env).dtor_names).Select(_1408_paramI);
              RAST._IExpr _1410_paramInit;
              DCOMP._IOwnership _1411___v68;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1412___v69;
              RAST._IExpr _out158;
              DCOMP._IOwnership _out159;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out160;
              (this).GenIdent(_1409_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out158, out _out159, out _out160);
              _1410_paramInit = _out158;
              _1411___v68 = _out159;
              _1412___v69 = _out160;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1409_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1410_paramInit)));
              if (((env).dtor_types).Contains(_1409_param)) {
                RAST._IType _1413_declaredType;
                _1413_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1409_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1409_param, _1413_declaredType);
              }
            }
            RAST._IExpr _1414_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1415_bodyIdents;
            DCOMP._IEnvironment _1416_bodyEnv;
            RAST._IExpr _out161;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out162;
            DCOMP._IEnvironment _out163;
            (this).GenStmts(_1407_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), newEnv, false, earlyReturn, out _out161, out _out162, out _out163);
            _1414_bodyExpr = _out161;
            _1415_bodyIdents = _out162;
            _1416_bodyEnv = _out163;
            readIdents = _1415_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1414_bodyExpr)));
          }
        }
      }
      if (unmatched59) {
        if (_source59.is_JumpTailCallStart) {
          unmatched59 = false;
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched59) {
        if (_source59.is_Call) {
          DAST._IExpression _1417_on = _source59.dtor_on;
          DAST._ICallName _1418_name = _source59.dtor_callName;
          Dafny.ISequence<DAST._IType> _1419_typeArgs = _source59.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1420_args = _source59.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1421_maybeOutVars = _source59.dtor_outs;
          unmatched59 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IExpr _1422_onExpr;
            DCOMP._IOwnership _1423___v70;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1424_enclosingIdents;
            RAST._IExpr _out164;
            DCOMP._IOwnership _out165;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out166;
            (this).GenExpr(_1417_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out164, out _out165, out _out166);
            _1422_onExpr = _out164;
            _1423___v70 = _out165;
            _1424_enclosingIdents = _out166;
            Dafny.ISequence<RAST._IType> _1425_typeArgsR;
            _1425_typeArgsR = Dafny.Sequence<RAST._IType>.FromElements();
            if ((new BigInteger((_1419_typeArgs).Count)) >= (BigInteger.One)) {
              BigInteger _1426_typeI;
              _1426_typeI = BigInteger.Zero;
              while ((_1426_typeI) < (new BigInteger((_1419_typeArgs).Count))) {
                RAST._IType _1427_tpe;
                RAST._IType _out167;
                _out167 = (this).GenType((_1419_typeArgs).Select(_1426_typeI), false, false);
                _1427_tpe = _out167;
                _1425_typeArgsR = Dafny.Sequence<RAST._IType>.Concat(_1425_typeArgsR, Dafny.Sequence<RAST._IType>.FromElements(_1427_tpe));
                _1426_typeI = (_1426_typeI) + (BigInteger.One);
              }
            }
            Dafny.ISequence<RAST._IExpr> _1428_argExprs;
            _1428_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi28 = new BigInteger((_1420_args).Count);
            for (BigInteger _1429_i = BigInteger.Zero; _1429_i < _hi28; _1429_i++) {
              DCOMP._IOwnership _1430_argOwnership;
              _1430_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              if (((_1418_name).is_CallName) && ((_1429_i) < (new BigInteger((((_1418_name).dtor_signature)).Count)))) {
                RAST._IType _1431_tpe;
                RAST._IType _out168;
                _out168 = (this).GenType(((((_1418_name).dtor_signature)).Select(_1429_i)).dtor_typ, false, false);
                _1431_tpe = _out168;
                if ((_1431_tpe).CanReadWithoutClone()) {
                  _1430_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
                }
              }
              RAST._IExpr _1432_argExpr;
              DCOMP._IOwnership _1433_ownership;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1434_argIdents;
              RAST._IExpr _out169;
              DCOMP._IOwnership _out170;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out171;
              (this).GenExpr((_1420_args).Select(_1429_i), selfIdent, env, _1430_argOwnership, out _out169, out _out170, out _out171);
              _1432_argExpr = _out169;
              _1433_ownership = _out170;
              _1434_argIdents = _out171;
              _1428_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1428_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1432_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1434_argIdents);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1424_enclosingIdents);
            Dafny.ISequence<Dafny.Rune> _1435_renderedName;
            _1435_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
              DAST._ICallName _source61 = _1418_name;
              bool unmatched61 = true;
              if (unmatched61) {
                if (_source61.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _1436_name = _source61.dtor_name;
                  Std.Wrappers._IOption<DAST._IType> _1437___v71 = _source61.dtor_onType;
                  Dafny.ISequence<DAST._IFormal> _1438___v72 = _source61.dtor_signature;
                  unmatched61 = false;
                  return DCOMP.__default.escapeName(_1436_name);
                }
              }
              if (unmatched61) {
                bool disjunctiveMatch9 = false;
                if (_source61.is_MapBuilderAdd) {
                  disjunctiveMatch9 = true;
                }
                if (_source61.is_SetBuilderAdd) {
                  disjunctiveMatch9 = true;
                }
                if (disjunctiveMatch9) {
                  unmatched61 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                }
              }
              if (unmatched61) {
                bool disjunctiveMatch10 = false;
                disjunctiveMatch10 = true;
                disjunctiveMatch10 = true;
                if (disjunctiveMatch10) {
                  unmatched61 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                }
              }
              throw new System.Exception("unexpected control point");
            }))();
            DAST._IExpression _source62 = _1417_on;
            bool unmatched62 = true;
            if (unmatched62) {
              if (_source62.is_Companion) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1439___v73 = _source62.dtor_Companion_a0;
                unmatched62 = false;
                {
                  _1422_onExpr = (_1422_onExpr).MSel(_1435_renderedName);
                }
              }
            }
            if (unmatched62) {
              DAST._IExpression _1440___v74 = _source62;
              unmatched62 = false;
              {
                _1422_onExpr = (_1422_onExpr).Sel(_1435_renderedName);
              }
            }
            generated = _1422_onExpr;
            if ((new BigInteger((_1425_typeArgsR).Count)).Sign == 1) {
              generated = (generated).ApplyType(_1425_typeArgsR);
            }
            generated = (generated).Apply(_1428_argExprs);
            if (((_1421_maybeOutVars).is_Some) && ((new BigInteger(((_1421_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1441_outVar;
              _1441_outVar = DCOMP.__default.escapeName((((_1421_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
              generated = RAST.__default.AssignVar(_1441_outVar, generated);
            } else if (((_1421_maybeOutVars).is_None) || ((new BigInteger(((_1421_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1442_tmpVar;
              _1442_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1443_tmpId;
              _1443_tmpId = RAST.Expr.create_Identifier(_1442_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1442_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1444_outVars;
              _1444_outVars = (_1421_maybeOutVars).dtor_value;
              BigInteger _hi29 = new BigInteger((_1444_outVars).Count);
              for (BigInteger _1445_outI = BigInteger.Zero; _1445_outI < _hi29; _1445_outI++) {
                Dafny.ISequence<Dafny.Rune> _1446_outVar;
                _1446_outVar = DCOMP.__default.escapeName(((_1444_outVars).Select(_1445_outI)));
                RAST._IExpr _1447_rhs;
                _1447_rhs = (_1443_tmpId).Sel(Std.Strings.__default.OfNat(_1445_outI));
                generated = (generated).Then(RAST.__default.AssignVar(_1446_outVar, _1447_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched59) {
        if (_source59.is_Return) {
          DAST._IExpression _1448_exprDafny = _source59.dtor_expr;
          unmatched59 = false;
          {
            RAST._IExpr _1449_expr;
            DCOMP._IOwnership _1450___v75;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1451_recIdents;
            RAST._IExpr _out172;
            DCOMP._IOwnership _out173;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out174;
            (this).GenExpr(_1448_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out172, out _out173, out _out174);
            _1449_expr = _out172;
            _1450___v75 = _out173;
            _1451_recIdents = _out174;
            readIdents = _1451_recIdents;
            if (isLast) {
              generated = _1449_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1449_expr));
            }
            newEnv = env;
          }
        }
      }
      if (unmatched59) {
        if (_source59.is_EarlyReturn) {
          unmatched59 = false;
          {
            generated = earlyReturn;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched59) {
        if (_source59.is_Halt) {
          unmatched59 = false;
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched59) {
        DAST._IExpression _1452_e = _source59.dtor_Print_a0;
        unmatched59 = false;
        {
          RAST._IExpr _1453_printedExpr;
          DCOMP._IOwnership _1454_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1455_recIdents;
          RAST._IExpr _out175;
          DCOMP._IOwnership _out176;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
          (this).GenExpr(_1452_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out175, out _out176, out _out177);
          _1453_printedExpr = _out175;
          _1454_recOwnership = _out176;
          _1455_recIdents = _out177;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1453_printedExpr)));
          readIdents = _1455_recIdents;
          newEnv = env;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source63 = range;
      bool unmatched63 = true;
      if (unmatched63) {
        if (_source63.is_NoRange) {
          unmatched63 = false;
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      if (unmatched63) {
        if (_source63.is_U8) {
          unmatched63 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      if (unmatched63) {
        if (_source63.is_U16) {
          unmatched63 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      if (unmatched63) {
        if (_source63.is_U32) {
          unmatched63 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      if (unmatched63) {
        if (_source63.is_U64) {
          unmatched63 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      if (unmatched63) {
        if (_source63.is_U128) {
          unmatched63 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      if (unmatched63) {
        if (_source63.is_I8) {
          unmatched63 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      if (unmatched63) {
        if (_source63.is_I16) {
          unmatched63 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      if (unmatched63) {
        if (_source63.is_I32) {
          unmatched63 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      if (unmatched63) {
        if (_source63.is_I64) {
          unmatched63 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      if (unmatched63) {
        if (_source63.is_I128) {
          unmatched63 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
        }
      }
      if (unmatched63) {
        DAST._INewtypeRange _1456___v76 = _source63;
        unmatched63 = false;
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
      DAST._IExpression _source64 = e;
      bool unmatched64 = true;
      if (unmatched64) {
        if (_source64.is_Literal) {
          DAST._ILiteral _h150 = _source64.dtor_Literal_a0;
          if (_h150.is_BoolLiteral) {
            bool _1457_b = _h150.dtor_BoolLiteral_a0;
            unmatched64 = false;
            {
              RAST._IExpr _out182;
              DCOMP._IOwnership _out183;
              DCOMP.COMP.FromOwned(RAST.Expr.create_LiteralBool(_1457_b), expectedOwnership, out _out182, out _out183);
              r = _out182;
              resultingOwnership = _out183;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched64) {
        if (_source64.is_Literal) {
          DAST._ILiteral _h151 = _source64.dtor_Literal_a0;
          if (_h151.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1458_i = _h151.dtor_IntLiteral_a0;
            DAST._IType _1459_t = _h151.dtor_IntLiteral_a1;
            unmatched64 = false;
            {
              DAST._IType _source65 = _1459_t;
              bool unmatched65 = true;
              if (unmatched65) {
                if (_source65.is_Primitive) {
                  DAST._IPrimitive _h90 = _source65.dtor_Primitive_a0;
                  if (_h90.is_Int) {
                    unmatched65 = false;
                    {
                      if ((new BigInteger((_1458_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1458_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1458_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched65) {
                DAST._IType _1460_o = _source65;
                unmatched65 = false;
                {
                  RAST._IType _1461_genType;
                  RAST._IType _out184;
                  _out184 = (this).GenType(_1460_o, false, false);
                  _1461_genType = _out184;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1458_i), _1461_genType);
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
      if (unmatched64) {
        if (_source64.is_Literal) {
          DAST._ILiteral _h152 = _source64.dtor_Literal_a0;
          if (_h152.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1462_n = _h152.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1463_d = _h152.dtor_DecLiteral_a1;
            DAST._IType _1464_t = _h152.dtor_DecLiteral_a2;
            unmatched64 = false;
            {
              DAST._IType _source66 = _1464_t;
              bool unmatched66 = true;
              if (unmatched66) {
                if (_source66.is_Primitive) {
                  DAST._IPrimitive _h91 = _source66.dtor_Primitive_a0;
                  if (_h91.is_Real) {
                    unmatched66 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1462_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1463_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched66) {
                DAST._IType _1465_o = _source66;
                unmatched66 = false;
                {
                  RAST._IType _1466_genType;
                  RAST._IType _out187;
                  _out187 = (this).GenType(_1465_o, false, false);
                  _1466_genType = _out187;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1462_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1463_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1466_genType);
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
      if (unmatched64) {
        if (_source64.is_Literal) {
          DAST._ILiteral _h153 = _source64.dtor_Literal_a0;
          if (_h153.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1467_l = _h153.dtor_StringLiteral_a0;
            bool _1468_verbatim = _h153.dtor_verbatim;
            unmatched64 = false;
            {
              if (_1468_verbatim) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Verbatim strings prefixed by @ not supported yet."));
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1467_l, false, _1468_verbatim));
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
      if (unmatched64) {
        if (_source64.is_Literal) {
          DAST._ILiteral _h154 = _source64.dtor_Literal_a0;
          if (_h154.is_CharLiteralUTF16) {
            BigInteger _1469_c = _h154.dtor_CharLiteralUTF16_a0;
            unmatched64 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1469_c));
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
      if (unmatched64) {
        if (_source64.is_Literal) {
          DAST._ILiteral _h155 = _source64.dtor_Literal_a0;
          if (_h155.is_CharLiteral) {
            Dafny.Rune _1470_c = _h155.dtor_CharLiteral_a0;
            unmatched64 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1470_c).Value)));
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
      if (unmatched64) {
        DAST._ILiteral _h156 = _source64.dtor_Literal_a0;
        DAST._IType _1471_tpe = _h156.dtor_Null_a0;
        unmatched64 = false;
        {
          RAST._IType _1472_tpeGen;
          RAST._IType _out196;
          _out196 = (this).GenType(_1471_tpe, false, false);
          _1472_tpeGen = _out196;
          r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None")), _1472_tpeGen);
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
      DAST._IBinOp _1473_op = _let_tmp_rhs52.dtor_op;
      DAST._IExpression _1474_lExpr = _let_tmp_rhs52.dtor_left;
      DAST._IExpression _1475_rExpr = _let_tmp_rhs52.dtor_right;
      DAST.Format._IBinaryOpFormat _1476_format = _let_tmp_rhs52.dtor_format2;
      bool _1477_becomesLeftCallsRight;
      _1477_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source67 = _1473_op;
        bool unmatched67 = true;
        if (unmatched67) {
          bool disjunctiveMatch11 = false;
          if (_source67.is_SetMerge) {
            disjunctiveMatch11 = true;
          }
          if (_source67.is_SetSubtraction) {
            disjunctiveMatch11 = true;
          }
          if (_source67.is_SetIntersection) {
            disjunctiveMatch11 = true;
          }
          if (_source67.is_SetDisjoint) {
            disjunctiveMatch11 = true;
          }
          if (_source67.is_MapMerge) {
            disjunctiveMatch11 = true;
          }
          if (_source67.is_MapSubtraction) {
            disjunctiveMatch11 = true;
          }
          if (_source67.is_MultisetMerge) {
            disjunctiveMatch11 = true;
          }
          if (_source67.is_MultisetSubtraction) {
            disjunctiveMatch11 = true;
          }
          if (_source67.is_MultisetIntersection) {
            disjunctiveMatch11 = true;
          }
          if (_source67.is_MultisetDisjoint) {
            disjunctiveMatch11 = true;
          }
          if (_source67.is_Concat) {
            disjunctiveMatch11 = true;
          }
          if (disjunctiveMatch11) {
            unmatched67 = false;
            return true;
          }
        }
        if (unmatched67) {
          DAST._IBinOp _1478___v77 = _source67;
          unmatched67 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1479_becomesRightCallsLeft;
      _1479_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source68 = _1473_op;
        bool unmatched68 = true;
        if (unmatched68) {
          if (_source68.is_In) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          DAST._IBinOp _1480___v78 = _source68;
          unmatched68 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1481_becomesCallLeftRight;
      _1481_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source69 = _1473_op;
        bool unmatched69 = true;
        if (unmatched69) {
          if (_source69.is_Eq) {
            bool referential0 = _source69.dtor_referential;
            if ((referential0) == (true)) {
              bool nullable0 = _source69.dtor_nullable;
              if ((nullable0) == (false)) {
                unmatched69 = false;
                return true;
              }
            }
          }
        }
        if (unmatched69) {
          if (_source69.is_SetMerge) {
            unmatched69 = false;
            return true;
          }
        }
        if (unmatched69) {
          if (_source69.is_SetSubtraction) {
            unmatched69 = false;
            return true;
          }
        }
        if (unmatched69) {
          if (_source69.is_SetIntersection) {
            unmatched69 = false;
            return true;
          }
        }
        if (unmatched69) {
          if (_source69.is_SetDisjoint) {
            unmatched69 = false;
            return true;
          }
        }
        if (unmatched69) {
          if (_source69.is_MapMerge) {
            unmatched69 = false;
            return true;
          }
        }
        if (unmatched69) {
          if (_source69.is_MapSubtraction) {
            unmatched69 = false;
            return true;
          }
        }
        if (unmatched69) {
          if (_source69.is_MultisetMerge) {
            unmatched69 = false;
            return true;
          }
        }
        if (unmatched69) {
          if (_source69.is_MultisetSubtraction) {
            unmatched69 = false;
            return true;
          }
        }
        if (unmatched69) {
          if (_source69.is_MultisetIntersection) {
            unmatched69 = false;
            return true;
          }
        }
        if (unmatched69) {
          if (_source69.is_MultisetDisjoint) {
            unmatched69 = false;
            return true;
          }
        }
        if (unmatched69) {
          if (_source69.is_Concat) {
            unmatched69 = false;
            return true;
          }
        }
        if (unmatched69) {
          DAST._IBinOp _1482___v79 = _source69;
          unmatched69 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      DCOMP._IOwnership _1483_expectedLeftOwnership;
      _1483_expectedLeftOwnership = ((_1477_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1479_becomesRightCallsLeft) || (_1481_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1484_expectedRightOwnership;
      _1484_expectedRightOwnership = (((_1477_becomesLeftCallsRight) || (_1481_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1479_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1485_left;
      DCOMP._IOwnership _1486___v80;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1487_recIdentsL;
      RAST._IExpr _out199;
      DCOMP._IOwnership _out200;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out201;
      (this).GenExpr(_1474_lExpr, selfIdent, env, _1483_expectedLeftOwnership, out _out199, out _out200, out _out201);
      _1485_left = _out199;
      _1486___v80 = _out200;
      _1487_recIdentsL = _out201;
      RAST._IExpr _1488_right;
      DCOMP._IOwnership _1489___v81;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1490_recIdentsR;
      RAST._IExpr _out202;
      DCOMP._IOwnership _out203;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out204;
      (this).GenExpr(_1475_rExpr, selfIdent, env, _1484_expectedRightOwnership, out _out202, out _out203, out _out204);
      _1488_right = _out202;
      _1489___v81 = _out203;
      _1490_recIdentsR = _out204;
      DAST._IBinOp _source70 = _1473_op;
      bool unmatched70 = true;
      if (unmatched70) {
        if (_source70.is_In) {
          unmatched70 = false;
          {
            r = ((_1488_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1485_left);
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_SeqProperPrefix) {
          unmatched70 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1485_left, _1488_right, _1476_format);
        }
      }
      if (unmatched70) {
        if (_source70.is_SeqPrefix) {
          unmatched70 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1485_left, _1488_right, _1476_format);
        }
      }
      if (unmatched70) {
        if (_source70.is_SetMerge) {
          unmatched70 = false;
          {
            r = ((_1485_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1488_right);
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_SetSubtraction) {
          unmatched70 = false;
          {
            r = ((_1485_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1488_right);
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_SetIntersection) {
          unmatched70 = false;
          {
            r = ((_1485_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1488_right);
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_Subset) {
          unmatched70 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1485_left, _1488_right, _1476_format);
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_ProperSubset) {
          unmatched70 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1485_left, _1488_right, _1476_format);
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_SetDisjoint) {
          unmatched70 = false;
          {
            r = ((_1485_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1488_right);
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_MapMerge) {
          unmatched70 = false;
          {
            r = ((_1485_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1488_right);
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_MapSubtraction) {
          unmatched70 = false;
          {
            r = ((_1485_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1488_right);
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_MultisetMerge) {
          unmatched70 = false;
          {
            r = ((_1485_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1488_right);
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_MultisetSubtraction) {
          unmatched70 = false;
          {
            r = ((_1485_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1488_right);
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_MultisetIntersection) {
          unmatched70 = false;
          {
            r = ((_1485_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1488_right);
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_Submultiset) {
          unmatched70 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1485_left, _1488_right, _1476_format);
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_ProperSubmultiset) {
          unmatched70 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1485_left, _1488_right, _1476_format);
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_MultisetDisjoint) {
          unmatched70 = false;
          {
            r = ((_1485_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1488_right);
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_Concat) {
          unmatched70 = false;
          {
            r = ((_1485_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1488_right);
          }
        }
      }
      if (unmatched70) {
        DAST._IBinOp _1491___v82 = _source70;
        unmatched70 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1473_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1473_op), _1485_left, _1488_right, _1476_format);
          } else {
            DAST._IBinOp _source71 = _1473_op;
            bool unmatched71 = true;
            if (unmatched71) {
              if (_source71.is_Eq) {
                bool _1492_referential = _source71.dtor_referential;
                bool _1493_nullable = _source71.dtor_nullable;
                unmatched71 = false;
                {
                  if (_1492_referential) {
                    if (_1493_nullable) {
                      r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1485_left, _1488_right));
                    } else {
                      r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1485_left, _1488_right));
                    }
                  } else {
                    r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1485_left, _1488_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                  }
                }
              }
            }
            if (unmatched71) {
              if (_source71.is_EuclidianDiv) {
                unmatched71 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1485_left, _1488_right));
                }
              }
            }
            if (unmatched71) {
              if (_source71.is_EuclidianMod) {
                unmatched71 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1485_left, _1488_right));
                }
              }
            }
            if (unmatched71) {
              Dafny.ISequence<Dafny.Rune> _1494_op = _source71.dtor_Passthrough_a0;
              unmatched71 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1494_op, _1485_left, _1488_right, _1476_format);
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
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1487_recIdentsL, _1490_recIdentsR);
      return ;
    }
    public void GenExprConvertFromNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs53 = e;
      DAST._IExpression _1495_expr = _let_tmp_rhs53.dtor_value;
      DAST._IType _1496_fromTpe = _let_tmp_rhs53.dtor_from;
      DAST._IType _1497_toTpe = _let_tmp_rhs53.dtor_typ;
      RAST._IExpr _1498_recursiveGen;
      DCOMP._IOwnership _1499_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1500_recIdents;
      RAST._IExpr _out207;
      DCOMP._IOwnership _out208;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out209;
      (this).GenExpr(_1495_expr, selfIdent, env, expectedOwnership, out _out207, out _out208, out _out209);
      _1498_recursiveGen = _out207;
      _1499_recOwned = _out208;
      _1500_recIdents = _out209;
      r = _1498_recursiveGen;
      if (object.Equals(_1499_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      RAST._IExpr _out210;
      DCOMP._IOwnership _out211;
      DCOMP.COMP.FromOwnership(r, _1499_recOwned, expectedOwnership, out _out210, out _out211);
      r = _out210;
      resultingOwnership = _out211;
      readIdents = _1500_recIdents;
    }
    public void GenExprConvertToNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IExpression _1501_expr = _let_tmp_rhs54.dtor_value;
      DAST._IType _1502_fromTpe = _let_tmp_rhs54.dtor_from;
      DAST._IType _1503_toTpe = _let_tmp_rhs54.dtor_typ;
      RAST._IExpr _1504_recursiveGen;
      DCOMP._IOwnership _1505_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1506_recIdents;
      RAST._IExpr _out212;
      DCOMP._IOwnership _out213;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out214;
      (this).GenExpr(_1501_expr, selfIdent, env, expectedOwnership, out _out212, out _out213, out _out214);
      _1504_recursiveGen = _out212;
      _1505_recOwned = _out213;
      _1506_recIdents = _out214;
      r = _1504_recursiveGen;
      if (object.Equals(_1505_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
      RAST._IExpr _out215;
      DCOMP._IOwnership _out216;
      DCOMP.COMP.FromOwnership(r, _1505_recOwned, expectedOwnership, out _out215, out _out216);
      r = _out215;
      resultingOwnership = _out216;
      readIdents = _1506_recIdents;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _1507_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _1508_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _1509_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _1509_toTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1510___v83 = _let_tmp_rhs56.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _1511___v84 = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      DAST._IType _1512_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _1513_range = _let_tmp_rhs57.dtor_range;
      bool _1514_erase = _let_tmp_rhs57.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1515_attributes = _let_tmp_rhs57.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _1516_nativeToType;
      _1516_nativeToType = DCOMP.COMP.NewtypeToRustType(_1512_b, _1513_range);
      if (object.Equals(_1508_fromTpe, _1512_b)) {
        RAST._IExpr _1517_recursiveGen;
        DCOMP._IOwnership _1518_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1519_recIdents;
        RAST._IExpr _out217;
        DCOMP._IOwnership _out218;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out219;
        (this).GenExpr(_1507_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out217, out _out218, out _out219);
        _1517_recursiveGen = _out217;
        _1518_recOwned = _out218;
        _1519_recIdents = _out219;
        readIdents = _1519_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source72 = _1516_nativeToType;
        bool unmatched72 = true;
        if (unmatched72) {
          if (_source72.is_Some) {
            RAST._IType _1520_v = _source72.dtor_value;
            unmatched72 = false;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1517_recursiveGen, RAST.Expr.create_ExprFromType(_1520_v)));
            RAST._IExpr _out220;
            DCOMP._IOwnership _out221;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out220, out _out221);
            r = _out220;
            resultingOwnership = _out221;
          }
        }
        if (unmatched72) {
          unmatched72 = false;
          if (_1514_erase) {
            r = _1517_recursiveGen;
          } else {
            RAST._IType _1521_rhsType;
            RAST._IType _out222;
            _out222 = (this).GenType(_1509_toTpe, true, false);
            _1521_rhsType = _out222;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1521_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1517_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out223;
          DCOMP._IOwnership _out224;
          DCOMP.COMP.FromOwnership(r, _1518_recOwned, expectedOwnership, out _out223, out _out224);
          r = _out223;
          resultingOwnership = _out224;
        }
      } else {
        if ((_1516_nativeToType).is_Some) {
          DAST._IType _source73 = _1508_fromTpe;
          bool unmatched73 = true;
          if (unmatched73) {
            if (_source73.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1522___v85 = _source73.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _1523___v86 = _source73.dtor_typeArgs;
              DAST._IResolvedType resolved1 = _source73.dtor_resolved;
              if (resolved1.is_Newtype) {
                DAST._IType _1524_b0 = resolved1.dtor_baseType;
                DAST._INewtypeRange _1525_range0 = resolved1.dtor_range;
                bool _1526_erase0 = resolved1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1527_attributes0 = resolved1.dtor_attributes;
                unmatched73 = false;
                {
                  Std.Wrappers._IOption<RAST._IType> _1528_nativeFromType;
                  _1528_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1524_b0, _1525_range0);
                  if ((_1528_nativeFromType).is_Some) {
                    RAST._IExpr _1529_recursiveGen;
                    DCOMP._IOwnership _1530_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1531_recIdents;
                    RAST._IExpr _out225;
                    DCOMP._IOwnership _out226;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out227;
                    (this).GenExpr(_1507_expr, selfIdent, env, expectedOwnership, out _out225, out _out226, out _out227);
                    _1529_recursiveGen = _out225;
                    _1530_recOwned = _out226;
                    _1531_recIdents = _out227;
                    RAST._IExpr _out228;
                    DCOMP._IOwnership _out229;
                    DCOMP.COMP.FromOwnership(RAST.Expr.create_TypeAscription(_1529_recursiveGen, (_1516_nativeToType).dtor_value), _1530_recOwned, expectedOwnership, out _out228, out _out229);
                    r = _out228;
                    resultingOwnership = _out229;
                    readIdents = _1531_recIdents;
                    return ;
                  }
                }
              }
            }
          }
          if (unmatched73) {
            DAST._IType _1532___v87 = _source73;
            unmatched73 = false;
          }
          if (object.Equals(_1508_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1533_recursiveGen;
            DCOMP._IOwnership _1534_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1535_recIdents;
            RAST._IExpr _out230;
            DCOMP._IOwnership _out231;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out232;
            (this).GenExpr(_1507_expr, selfIdent, env, expectedOwnership, out _out230, out _out231, out _out232);
            _1533_recursiveGen = _out230;
            _1534_recOwned = _out231;
            _1535_recIdents = _out232;
            RAST._IExpr _out233;
            DCOMP._IOwnership _out234;
            DCOMP.COMP.FromOwnership(RAST.Expr.create_TypeAscription((_1533_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1516_nativeToType).dtor_value), _1534_recOwned, expectedOwnership, out _out233, out _out234);
            r = _out233;
            resultingOwnership = _out234;
            readIdents = _1535_recIdents;
            return ;
          }
        }
        RAST._IExpr _out235;
        DCOMP._IOwnership _out236;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out237;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1507_expr, _1508_fromTpe, _1512_b), _1512_b, _1509_toTpe), selfIdent, env, expectedOwnership, out _out235, out _out236, out _out237);
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
      DAST._IExpression _1536_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _1537_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _1538_toTpe = _let_tmp_rhs58.dtor_typ;
      DAST._IType _let_tmp_rhs59 = _1537_fromTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1539___v88 = _let_tmp_rhs59.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _1540___v89 = _let_tmp_rhs59.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs60 = _let_tmp_rhs59.dtor_resolved;
      DAST._IType _1541_b = _let_tmp_rhs60.dtor_baseType;
      DAST._INewtypeRange _1542_range = _let_tmp_rhs60.dtor_range;
      bool _1543_erase = _let_tmp_rhs60.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1544_attributes = _let_tmp_rhs60.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _1545_nativeFromType;
      _1545_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1541_b, _1542_range);
      if (object.Equals(_1541_b, _1538_toTpe)) {
        RAST._IExpr _1546_recursiveGen;
        DCOMP._IOwnership _1547_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1548_recIdents;
        RAST._IExpr _out238;
        DCOMP._IOwnership _out239;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out240;
        (this).GenExpr(_1536_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out238, out _out239, out _out240);
        _1546_recursiveGen = _out238;
        _1547_recOwned = _out239;
        _1548_recIdents = _out240;
        readIdents = _1548_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source74 = _1545_nativeFromType;
        bool unmatched74 = true;
        if (unmatched74) {
          if (_source74.is_Some) {
            RAST._IType _1549_v = _source74.dtor_value;
            unmatched74 = false;
            RAST._IType _1550_toTpeRust;
            RAST._IType _out241;
            _out241 = (this).GenType(_1538_toTpe, false, false);
            _1550_toTpeRust = _out241;
            r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1550_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1546_recursiveGen));
            RAST._IExpr _out242;
            DCOMP._IOwnership _out243;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out242, out _out243);
            r = _out242;
            resultingOwnership = _out243;
          }
        }
        if (unmatched74) {
          unmatched74 = false;
          if (_1543_erase) {
            r = _1546_recursiveGen;
          } else {
            r = (_1546_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out244;
          DCOMP._IOwnership _out245;
          DCOMP.COMP.FromOwnership(r, _1547_recOwned, expectedOwnership, out _out244, out _out245);
          r = _out244;
          resultingOwnership = _out245;
        }
      } else {
        if ((_1545_nativeFromType).is_Some) {
          if (object.Equals(_1538_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1551_recursiveGen;
            DCOMP._IOwnership _1552_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1553_recIdents;
            RAST._IExpr _out246;
            DCOMP._IOwnership _out247;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out248;
            (this).GenExpr(_1536_expr, selfIdent, env, expectedOwnership, out _out246, out _out247, out _out248);
            _1551_recursiveGen = _out246;
            _1552_recOwned = _out247;
            _1553_recIdents = _out248;
            RAST._IExpr _out249;
            DCOMP._IOwnership _out250;
            DCOMP.COMP.FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1551_recursiveGen, (this).DafnyCharUnderlying)), _1552_recOwned, expectedOwnership, out _out249, out _out250);
            r = _out249;
            resultingOwnership = _out250;
            readIdents = _1553_recIdents;
            return ;
          }
        }
        RAST._IExpr _out251;
        DCOMP._IOwnership _out252;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out253;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1536_expr, _1537_fromTpe, _1541_b), _1541_b, _1538_toTpe), selfIdent, env, expectedOwnership, out _out251, out _out252, out _out253);
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
      DAST._IExpression _1554_expr = _let_tmp_rhs61.dtor_value;
      DAST._IType _1555_fromTpe = _let_tmp_rhs61.dtor_from;
      DAST._IType _1556_toTpe = _let_tmp_rhs61.dtor_typ;
      RAST._IType _1557_fromTpeGen;
      RAST._IType _out254;
      _out254 = (this).GenType(_1555_fromTpe, true, false);
      _1557_fromTpeGen = _out254;
      RAST._IType _1558_toTpeGen;
      RAST._IType _out255;
      _out255 = (this).GenType(_1556_toTpe, true, false);
      _1558_toTpeGen = _out255;
      RAST._IExpr _1559_recursiveGen;
      DCOMP._IOwnership _1560_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1561_recIdents;
      RAST._IExpr _out256;
      DCOMP._IOwnership _out257;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out258;
      (this).GenExpr(_1554_expr, selfIdent, env, expectedOwnership, out _out256, out _out257, out _out258);
      _1559_recursiveGen = _out256;
      _1560_recOwned = _out257;
      _1561_recIdents = _out258;
      Dafny.ISequence<Dafny.Rune> _1562_msg;
      _1562_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1557_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1558_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1562_msg);
      r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1559_recursiveGen)._ToString(DCOMP.__default.IND), _1562_msg));
      RAST._IExpr _out259;
      DCOMP._IOwnership _out260;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out259, out _out260);
      r = _out259;
      resultingOwnership = _out260;
      readIdents = _1561_recIdents;
    }
    public void GenExprConvert(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs62 = e;
      DAST._IExpression _1563_expr = _let_tmp_rhs62.dtor_value;
      DAST._IType _1564_fromTpe = _let_tmp_rhs62.dtor_from;
      DAST._IType _1565_toTpe = _let_tmp_rhs62.dtor_typ;
      if (object.Equals(_1564_fromTpe, _1565_toTpe)) {
        RAST._IExpr _1566_recursiveGen;
        DCOMP._IOwnership _1567_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1568_recIdents;
        RAST._IExpr _out261;
        DCOMP._IOwnership _out262;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out263;
        (this).GenExpr(_1563_expr, selfIdent, env, expectedOwnership, out _out261, out _out262, out _out263);
        _1566_recursiveGen = _out261;
        _1567_recOwned = _out262;
        _1568_recIdents = _out263;
        r = _1566_recursiveGen;
        RAST._IExpr _out264;
        DCOMP._IOwnership _out265;
        DCOMP.COMP.FromOwnership(r, _1567_recOwned, expectedOwnership, out _out264, out _out265);
        r = _out264;
        resultingOwnership = _out265;
        readIdents = _1568_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source75 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1564_fromTpe, _1565_toTpe);
        bool unmatched75 = true;
        if (unmatched75) {
          DAST._IType _01 = _source75.dtor__0;
          if (_01.is_Nullable) {
            DAST._IType _1569___v90 = _01.dtor_Nullable_a0;
            DAST._IType _1570___v91 = _source75.dtor__1;
            unmatched75 = false;
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
        if (unmatched75) {
          DAST._IType _1571___v92 = _source75.dtor__0;
          DAST._IType _11 = _source75.dtor__1;
          if (_11.is_Nullable) {
            DAST._IType _1572___v93 = _11.dtor_Nullable_a0;
            unmatched75 = false;
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
        if (unmatched75) {
          DAST._IType _1573___v94 = _source75.dtor__0;
          DAST._IType _12 = _source75.dtor__1;
          if (_12.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1574___v95 = _12.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1575___v96 = _12.dtor_typeArgs;
            DAST._IResolvedType resolved2 = _12.dtor_resolved;
            if (resolved2.is_Newtype) {
              DAST._IType _1576_b = resolved2.dtor_baseType;
              DAST._INewtypeRange _1577_range = resolved2.dtor_range;
              bool _1578_erase = resolved2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1579_attributes = resolved2.dtor_attributes;
              unmatched75 = false;
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
        if (unmatched75) {
          DAST._IType _02 = _source75.dtor__0;
          if (_02.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1580___v97 = _02.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1581___v98 = _02.dtor_typeArgs;
            DAST._IResolvedType resolved3 = _02.dtor_resolved;
            if (resolved3.is_Newtype) {
              DAST._IType _1582_b = resolved3.dtor_baseType;
              DAST._INewtypeRange _1583_range = resolved3.dtor_range;
              bool _1584_erase = resolved3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1585_attributes = resolved3.dtor_attributes;
              DAST._IType _1586___v99 = _source75.dtor__1;
              unmatched75 = false;
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
        if (unmatched75) {
          DAST._IType _03 = _source75.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h92 = _03.dtor_Primitive_a0;
            if (_h92.is_Int) {
              DAST._IType _13 = _source75.dtor__1;
              if (_13.is_Primitive) {
                DAST._IPrimitive _h93 = _13.dtor_Primitive_a0;
                if (_h93.is_Real) {
                  unmatched75 = false;
                  {
                    RAST._IExpr _1587_recursiveGen;
                    DCOMP._IOwnership _1588___v100;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1589_recIdents;
                    RAST._IExpr _out278;
                    DCOMP._IOwnership _out279;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out280;
                    (this).GenExpr(_1563_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out278, out _out279, out _out280);
                    _1587_recursiveGen = _out278;
                    _1588___v100 = _out279;
                    _1589_recIdents = _out280;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1587_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out281;
                    DCOMP._IOwnership _out282;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out281, out _out282);
                    r = _out281;
                    resultingOwnership = _out282;
                    readIdents = _1589_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched75) {
          DAST._IType _04 = _source75.dtor__0;
          if (_04.is_Primitive) {
            DAST._IPrimitive _h94 = _04.dtor_Primitive_a0;
            if (_h94.is_Real) {
              DAST._IType _14 = _source75.dtor__1;
              if (_14.is_Primitive) {
                DAST._IPrimitive _h95 = _14.dtor_Primitive_a0;
                if (_h95.is_Int) {
                  unmatched75 = false;
                  {
                    RAST._IExpr _1590_recursiveGen;
                    DCOMP._IOwnership _1591___v101;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1592_recIdents;
                    RAST._IExpr _out283;
                    DCOMP._IOwnership _out284;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out285;
                    (this).GenExpr(_1563_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out283, out _out284, out _out285);
                    _1590_recursiveGen = _out283;
                    _1591___v101 = _out284;
                    _1592_recIdents = _out285;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1590_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out286;
                    DCOMP._IOwnership _out287;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out286, out _out287);
                    r = _out286;
                    resultingOwnership = _out287;
                    readIdents = _1592_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched75) {
          DAST._IType _05 = _source75.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h96 = _05.dtor_Primitive_a0;
            if (_h96.is_Int) {
              DAST._IType _15 = _source75.dtor__1;
              if (_15.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1593___v102 = _15.dtor_Passthrough_a0;
                unmatched75 = false;
                {
                  RAST._IType _1594_rhsType;
                  RAST._IType _out288;
                  _out288 = (this).GenType(_1565_toTpe, true, false);
                  _1594_rhsType = _out288;
                  RAST._IExpr _1595_recursiveGen;
                  DCOMP._IOwnership _1596___v103;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1597_recIdents;
                  RAST._IExpr _out289;
                  DCOMP._IOwnership _out290;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out291;
                  (this).GenExpr(_1563_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out289, out _out290, out _out291);
                  _1595_recursiveGen = _out289;
                  _1596___v103 = _out290;
                  _1597_recIdents = _out291;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1594_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1595_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out292;
                  DCOMP._IOwnership _out293;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out292, out _out293);
                  r = _out292;
                  resultingOwnership = _out293;
                  readIdents = _1597_recIdents;
                }
              }
            }
          }
        }
        if (unmatched75) {
          DAST._IType _06 = _source75.dtor__0;
          if (_06.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1598___v104 = _06.dtor_Passthrough_a0;
            DAST._IType _16 = _source75.dtor__1;
            if (_16.is_Primitive) {
              DAST._IPrimitive _h97 = _16.dtor_Primitive_a0;
              if (_h97.is_Int) {
                unmatched75 = false;
                {
                  RAST._IType _1599_rhsType;
                  RAST._IType _out294;
                  _out294 = (this).GenType(_1564_fromTpe, true, false);
                  _1599_rhsType = _out294;
                  RAST._IExpr _1600_recursiveGen;
                  DCOMP._IOwnership _1601___v105;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1602_recIdents;
                  RAST._IExpr _out295;
                  DCOMP._IOwnership _out296;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out297;
                  (this).GenExpr(_1563_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out295, out _out296, out _out297);
                  _1600_recursiveGen = _out295;
                  _1601___v105 = _out296;
                  _1602_recIdents = _out297;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::dafny_runtime::BigInt::from("), (_1600_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")}")));
                  RAST._IExpr _out298;
                  DCOMP._IOwnership _out299;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out298, out _out299);
                  r = _out298;
                  resultingOwnership = _out299;
                  readIdents = _1602_recIdents;
                }
              }
            }
          }
        }
        if (unmatched75) {
          DAST._IType _07 = _source75.dtor__0;
          if (_07.is_Primitive) {
            DAST._IPrimitive _h98 = _07.dtor_Primitive_a0;
            if (_h98.is_Int) {
              DAST._IType _17 = _source75.dtor__1;
              if (_17.is_Primitive) {
                DAST._IPrimitive _h99 = _17.dtor_Primitive_a0;
                if (_h99.is_Char) {
                  unmatched75 = false;
                  {
                    RAST._IType _1603_rhsType;
                    RAST._IType _out300;
                    _out300 = (this).GenType(_1565_toTpe, true, false);
                    _1603_rhsType = _out300;
                    RAST._IExpr _1604_recursiveGen;
                    DCOMP._IOwnership _1605___v106;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1606_recIdents;
                    RAST._IExpr _out301;
                    DCOMP._IOwnership _out302;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out303;
                    (this).GenExpr(_1563_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out301, out _out302, out _out303);
                    _1604_recursiveGen = _out301;
                    _1605___v106 = _out302;
                    _1606_recIdents = _out303;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), (_1604_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()")));
                    RAST._IExpr _out304;
                    DCOMP._IOwnership _out305;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out304, out _out305);
                    r = _out304;
                    resultingOwnership = _out305;
                    readIdents = _1606_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched75) {
          DAST._IType _08 = _source75.dtor__0;
          if (_08.is_Primitive) {
            DAST._IPrimitive _h910 = _08.dtor_Primitive_a0;
            if (_h910.is_Char) {
              DAST._IType _18 = _source75.dtor__1;
              if (_18.is_Primitive) {
                DAST._IPrimitive _h911 = _18.dtor_Primitive_a0;
                if (_h911.is_Int) {
                  unmatched75 = false;
                  {
                    RAST._IType _1607_rhsType;
                    RAST._IType _out306;
                    _out306 = (this).GenType(_1564_fromTpe, true, false);
                    _1607_rhsType = _out306;
                    RAST._IExpr _1608_recursiveGen;
                    DCOMP._IOwnership _1609___v107;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1610_recIdents;
                    RAST._IExpr _out307;
                    DCOMP._IOwnership _out308;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out309;
                    (this).GenExpr(_1563_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out307, out _out308, out _out309);
                    _1608_recursiveGen = _out307;
                    _1609___v107 = _out308;
                    _1610_recIdents = _out309;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1608_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out310;
                    DCOMP._IOwnership _out311;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out310, out _out311);
                    r = _out310;
                    resultingOwnership = _out311;
                    readIdents = _1610_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched75) {
          DAST._IType _09 = _source75.dtor__0;
          if (_09.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1611___v108 = _09.dtor_Passthrough_a0;
            DAST._IType _19 = _source75.dtor__1;
            if (_19.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1612___v109 = _19.dtor_Passthrough_a0;
              unmatched75 = false;
              {
                RAST._IExpr _1613_recursiveGen;
                DCOMP._IOwnership _1614___v110;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1615_recIdents;
                RAST._IExpr _out312;
                DCOMP._IOwnership _out313;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out314;
                (this).GenExpr(_1563_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out312, out _out313, out _out314);
                _1613_recursiveGen = _out312;
                _1614___v110 = _out313;
                _1615_recIdents = _out314;
                RAST._IType _1616_toTpeGen;
                RAST._IType _out315;
                _out315 = (this).GenType(_1565_toTpe, true, false);
                _1616_toTpeGen = _out315;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1613_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1616_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out316;
                DCOMP._IOwnership _out317;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out316, out _out317);
                r = _out316;
                resultingOwnership = _out317;
                readIdents = _1615_recIdents;
              }
            }
          }
        }
        if (unmatched75) {
          _System._ITuple2<DAST._IType, DAST._IType> _1617___v111 = _source75;
          unmatched75 = false;
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
      Std.Wrappers._IOption<RAST._IType> _1618_tpe;
      _1618_tpe = (env).GetType(rName);
      bool _1619_currentlyBorrowed;
      _1619_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1620_noNeedOfClone;
      _1620_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        r = RAST.__default.BorrowMut(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        if (!(_1620_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1620_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1619_currentlyBorrowed) {
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
      DAST._IExpression _source76 = e;
      bool unmatched76 = true;
      if (unmatched76) {
        if (_source76.is_Literal) {
          DAST._ILiteral _1621___v112 = _source76.dtor_Literal_a0;
          unmatched76 = false;
          RAST._IExpr _out321;
          DCOMP._IOwnership _out322;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out323;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out321, out _out322, out _out323);
          r = _out321;
          resultingOwnership = _out322;
          readIdents = _out323;
        }
      }
      if (unmatched76) {
        if (_source76.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1622_name = _source76.dtor_Ident_a0;
          unmatched76 = false;
          {
            RAST._IExpr _out324;
            DCOMP._IOwnership _out325;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out326;
            (this).GenIdent(DCOMP.__default.escapeName(_1622_name), selfIdent, env, expectedOwnership, out _out324, out _out325, out _out326);
            r = _out324;
            resultingOwnership = _out325;
            readIdents = _out326;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1623_path = _source76.dtor_Companion_a0;
          unmatched76 = false;
          {
            RAST._IExpr _out327;
            _out327 = DCOMP.COMP.GenPathExpr(_1623_path);
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
      if (unmatched76) {
        if (_source76.is_InitializationValue) {
          DAST._IType _1624_typ = _source76.dtor_typ;
          unmatched76 = false;
          {
            RAST._IType _1625_typExpr;
            RAST._IType _out330;
            _out330 = (this).GenType(_1624_typ, false, false);
            _1625_typExpr = _out330;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1625_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
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
      if (unmatched76) {
        if (_source76.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _1626_values = _source76.dtor_Tuple_a0;
          unmatched76 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1627_exprs;
            _1627_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi30 = new BigInteger((_1626_values).Count);
            for (BigInteger _1628_i = BigInteger.Zero; _1628_i < _hi30; _1628_i++) {
              RAST._IExpr _1629_recursiveGen;
              DCOMP._IOwnership _1630___v113;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1631_recIdents;
              RAST._IExpr _out333;
              DCOMP._IOwnership _out334;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out335;
              (this).GenExpr((_1626_values).Select(_1628_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out333, out _out334, out _out335);
              _1629_recursiveGen = _out333;
              _1630___v113 = _out334;
              _1631_recIdents = _out335;
              _1627_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1627_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1629_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1631_recIdents);
            }
            r = (((new BigInteger((_1626_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_1627_exprs)) : (RAST.__default.SystemTuple(_1627_exprs)));
            RAST._IExpr _out336;
            DCOMP._IOwnership _out337;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out336, out _out337);
            r = _out336;
            resultingOwnership = _out337;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1632_path = _source76.dtor_path;
          Dafny.ISequence<DAST._IType> _1633_typeArgs = _source76.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1634_args = _source76.dtor_args;
          unmatched76 = false;
          {
            RAST._IExpr _out338;
            _out338 = DCOMP.COMP.GenPathExpr(_1632_path);
            r = _out338;
            if ((new BigInteger((_1633_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1635_typeExprs;
              _1635_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi31 = new BigInteger((_1633_typeArgs).Count);
              for (BigInteger _1636_i = BigInteger.Zero; _1636_i < _hi31; _1636_i++) {
                RAST._IType _1637_typeExpr;
                RAST._IType _out339;
                _out339 = (this).GenType((_1633_typeArgs).Select(_1636_i), false, false);
                _1637_typeExpr = _out339;
                _1635_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1635_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1637_typeExpr));
              }
              r = (r).ApplyType(_1635_typeExprs);
            }
            r = (r).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1638_arguments;
            _1638_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi32 = new BigInteger((_1634_args).Count);
            for (BigInteger _1639_i = BigInteger.Zero; _1639_i < _hi32; _1639_i++) {
              RAST._IExpr _1640_recursiveGen;
              DCOMP._IOwnership _1641___v114;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1642_recIdents;
              RAST._IExpr _out340;
              DCOMP._IOwnership _out341;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out342;
              (this).GenExpr((_1634_args).Select(_1639_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out340, out _out341, out _out342);
              _1640_recursiveGen = _out340;
              _1641___v114 = _out341;
              _1642_recIdents = _out342;
              _1638_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1638_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1640_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1642_recIdents);
            }
            r = (r).Apply(_1638_arguments);
            RAST._IExpr _out343;
            DCOMP._IOwnership _out344;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out343, out _out344);
            r = _out343;
            resultingOwnership = _out344;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_NewArray) {
          Dafny.ISequence<DAST._IExpression> _1643_dims = _source76.dtor_dims;
          DAST._IType _1644_typ = _source76.dtor_typ;
          unmatched76 = false;
          {
            BigInteger _1645_i;
            _1645_i = (new BigInteger((_1643_dims).Count)) - (BigInteger.One);
            RAST._IType _1646_genTyp;
            RAST._IType _out345;
            _out345 = (this).GenType(_1644_typ, false, false);
            _1646_genTyp = _out345;
            Dafny.ISequence<Dafny.Rune> _1647_s;
            _1647_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1646_genTyp)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::std::default::Default>::default()"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            while ((_1645_i).Sign != -1) {
              RAST._IExpr _1648_recursiveGen;
              DCOMP._IOwnership _1649___v115;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1650_recIdents;
              RAST._IExpr _out346;
              DCOMP._IOwnership _out347;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out348;
              (this).GenExpr((_1643_dims).Select(_1645_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out346, out _out347, out _out348);
              _1648_recursiveGen = _out346;
              _1649___v115 = _out347;
              _1650_recIdents = _out348;
              _1647_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), _1647_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), (_1648_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1650_recIdents);
              _1645_i = (_1645_i) - (BigInteger.One);
            }
            r = RAST.Expr.create_RawExpr(_1647_s);
            RAST._IExpr _out349;
            DCOMP._IOwnership _out350;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out349, out _out350);
            r = _out349;
            resultingOwnership = _out350;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_DatatypeValue) {
          DAST._IDatatypeType _1651_datatypeType = _source76.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1652_typeArgs = _source76.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1653_variant = _source76.dtor_variant;
          bool _1654_isCo = _source76.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1655_values = _source76.dtor_contents;
          unmatched76 = false;
          {
            RAST._IExpr _out351;
            _out351 = DCOMP.COMP.GenPathExpr((_1651_datatypeType).dtor_path);
            r = _out351;
            Dafny.ISequence<RAST._IType> _1656_genTypeArgs;
            _1656_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi33 = new BigInteger((_1652_typeArgs).Count);
            for (BigInteger _1657_i = BigInteger.Zero; _1657_i < _hi33; _1657_i++) {
              RAST._IType _1658_typeExpr;
              RAST._IType _out352;
              _out352 = (this).GenType((_1652_typeArgs).Select(_1657_i), false, false);
              _1658_typeExpr = _out352;
              _1656_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1656_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1658_typeExpr));
            }
            if ((new BigInteger((_1652_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1656_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1653_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1659_assignments;
            _1659_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi34 = new BigInteger((_1655_values).Count);
            for (BigInteger _1660_i = BigInteger.Zero; _1660_i < _hi34; _1660_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs63 = (_1655_values).Select(_1660_i);
              Dafny.ISequence<Dafny.Rune> _1661_name = _let_tmp_rhs63.dtor__0;
              DAST._IExpression _1662_value = _let_tmp_rhs63.dtor__1;
              if (_1654_isCo) {
                RAST._IExpr _1663_recursiveGen;
                DCOMP._IOwnership _1664___v116;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1665_recIdents;
                RAST._IExpr _out353;
                DCOMP._IOwnership _out354;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out355;
                (this).GenExpr(_1662_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out353, out _out354, out _out355);
                _1663_recursiveGen = _out353;
                _1664___v116 = _out354;
                _1665_recIdents = _out355;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1665_recIdents);
                Dafny.ISequence<Dafny.Rune> _1666_allReadCloned;
                _1666_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1665_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1667_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1665_recIdents).Elements) {
                    _1667_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1665_recIdents).Contains(_1667_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 3346)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1666_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1666_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1667_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1667_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1665_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1665_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1667_next));
                }
                Dafny.ISequence<Dafny.Rune> _1668_wasAssigned;
                _1668_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1666_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1663_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1659_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1659_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1661_name, RAST.Expr.create_RawExpr(_1668_wasAssigned))));
              } else {
                RAST._IExpr _1669_recursiveGen;
                DCOMP._IOwnership _1670___v117;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1671_recIdents;
                RAST._IExpr _out356;
                DCOMP._IOwnership _out357;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out358;
                (this).GenExpr(_1662_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out356, out _out357, out _out358);
                _1669_recursiveGen = _out356;
                _1670___v117 = _out357;
                _1671_recIdents = _out358;
                _1659_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1659_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1661_name, _1669_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1671_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1659_assignments);
            if ((this).IsRcWrapped((_1651_datatypeType).dtor_attributes)) {
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
      if (unmatched76) {
        if (_source76.is_Convert) {
          DAST._IExpression _1672___v118 = _source76.dtor_value;
          DAST._IType _1673___v119 = _source76.dtor_from;
          DAST._IType _1674___v120 = _source76.dtor_typ;
          unmatched76 = false;
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
      if (unmatched76) {
        if (_source76.is_SeqConstruct) {
          DAST._IExpression _1675_length = _source76.dtor_length;
          DAST._IExpression _1676_expr = _source76.dtor_elem;
          unmatched76 = false;
          {
            RAST._IExpr _1677_recursiveGen;
            DCOMP._IOwnership _1678___v121;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1679_recIdents;
            RAST._IExpr _out364;
            DCOMP._IOwnership _out365;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out366;
            (this).GenExpr(_1676_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out364, out _out365, out _out366);
            _1677_recursiveGen = _out364;
            _1678___v121 = _out365;
            _1679_recIdents = _out366;
            RAST._IExpr _1680_lengthGen;
            DCOMP._IOwnership _1681___v122;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1682_lengthIdents;
            RAST._IExpr _out367;
            DCOMP._IOwnership _out368;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out369;
            (this).GenExpr(_1675_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out367, out _out368, out _out369);
            _1680_lengthGen = _out367;
            _1681___v122 = _out368;
            _1682_lengthIdents = _out369;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1677_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1680_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1679_recIdents, _1682_lengthIdents);
            RAST._IExpr _out370;
            DCOMP._IOwnership _out371;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out370, out _out371);
            r = _out370;
            resultingOwnership = _out371;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _1683_exprs = _source76.dtor_elements;
          DAST._IType _1684_typ = _source76.dtor_typ;
          unmatched76 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1685_genTpe;
            RAST._IType _out372;
            _out372 = (this).GenType(_1684_typ, false, false);
            _1685_genTpe = _out372;
            BigInteger _1686_i;
            _1686_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1687_args;
            _1687_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1686_i) < (new BigInteger((_1683_exprs).Count))) {
              RAST._IExpr _1688_recursiveGen;
              DCOMP._IOwnership _1689___v123;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1690_recIdents;
              RAST._IExpr _out373;
              DCOMP._IOwnership _out374;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out375;
              (this).GenExpr((_1683_exprs).Select(_1686_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out373, out _out374, out _out375);
              _1688_recursiveGen = _out373;
              _1689___v123 = _out374;
              _1690_recIdents = _out375;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1690_recIdents);
              _1687_args = Dafny.Sequence<RAST._IExpr>.Concat(_1687_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1688_recursiveGen));
              _1686_i = (_1686_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_1687_args);
            if ((new BigInteger((_1687_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1685_genTpe));
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
      if (unmatched76) {
        if (_source76.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _1691_exprs = _source76.dtor_elements;
          unmatched76 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1692_generatedValues;
            _1692_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1693_i;
            _1693_i = BigInteger.Zero;
            while ((_1693_i) < (new BigInteger((_1691_exprs).Count))) {
              RAST._IExpr _1694_recursiveGen;
              DCOMP._IOwnership _1695___v124;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1696_recIdents;
              RAST._IExpr _out378;
              DCOMP._IOwnership _out379;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out380;
              (this).GenExpr((_1691_exprs).Select(_1693_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out378, out _out379, out _out380);
              _1694_recursiveGen = _out378;
              _1695___v124 = _out379;
              _1696_recIdents = _out380;
              _1692_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1692_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1694_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1696_recIdents);
              _1693_i = (_1693_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_1692_generatedValues);
            RAST._IExpr _out381;
            DCOMP._IOwnership _out382;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out381, out _out382);
            r = _out381;
            resultingOwnership = _out382;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _1697_exprs = _source76.dtor_elements;
          unmatched76 = false;
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
              RAST._IExpr _out383;
              DCOMP._IOwnership _out384;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out385;
              (this).GenExpr((_1697_exprs).Select(_1699_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out383, out _out384, out _out385);
              _1700_recursiveGen = _out383;
              _1701___v125 = _out384;
              _1702_recIdents = _out385;
              _1698_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1698_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1700_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1702_recIdents);
              _1699_i = (_1699_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_1698_generatedValues);
            RAST._IExpr _out386;
            DCOMP._IOwnership _out387;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out386, out _out387);
            r = _out386;
            resultingOwnership = _out387;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_ToMultiset) {
          DAST._IExpression _1703_expr = _source76.dtor_ToMultiset_a0;
          unmatched76 = false;
          {
            RAST._IExpr _1704_recursiveGen;
            DCOMP._IOwnership _1705___v126;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1706_recIdents;
            RAST._IExpr _out388;
            DCOMP._IOwnership _out389;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out390;
            (this).GenExpr(_1703_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out388, out _out389, out _out390);
            _1704_recursiveGen = _out388;
            _1705___v126 = _out389;
            _1706_recIdents = _out390;
            r = ((_1704_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _1706_recIdents;
            RAST._IExpr _out391;
            DCOMP._IOwnership _out392;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out391, out _out392);
            r = _out391;
            resultingOwnership = _out392;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1707_mapElems = _source76.dtor_mapElems;
          unmatched76 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1708_generatedValues;
            _1708_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1709_i;
            _1709_i = BigInteger.Zero;
            while ((_1709_i) < (new BigInteger((_1707_mapElems).Count))) {
              RAST._IExpr _1710_recursiveGenKey;
              DCOMP._IOwnership _1711___v127;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1712_recIdentsKey;
              RAST._IExpr _out393;
              DCOMP._IOwnership _out394;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out395;
              (this).GenExpr(((_1707_mapElems).Select(_1709_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out393, out _out394, out _out395);
              _1710_recursiveGenKey = _out393;
              _1711___v127 = _out394;
              _1712_recIdentsKey = _out395;
              RAST._IExpr _1713_recursiveGenValue;
              DCOMP._IOwnership _1714___v128;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1715_recIdentsValue;
              RAST._IExpr _out396;
              DCOMP._IOwnership _out397;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out398;
              (this).GenExpr(((_1707_mapElems).Select(_1709_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out396, out _out397, out _out398);
              _1713_recursiveGenValue = _out396;
              _1714___v128 = _out397;
              _1715_recIdentsValue = _out398;
              _1708_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1708_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1710_recursiveGenKey, _1713_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1712_recIdentsKey), _1715_recIdentsValue);
              _1709_i = (_1709_i) + (BigInteger.One);
            }
            _1709_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1716_arguments;
            _1716_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1709_i) < (new BigInteger((_1708_generatedValues).Count))) {
              RAST._IExpr _1717_genKey;
              _1717_genKey = ((_1708_generatedValues).Select(_1709_i)).dtor__0;
              RAST._IExpr _1718_genValue;
              _1718_genValue = ((_1708_generatedValues).Select(_1709_i)).dtor__1;
              _1716_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1716_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1717_genKey, _1718_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _1709_i = (_1709_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_1716_arguments);
            RAST._IExpr _out399;
            DCOMP._IOwnership _out400;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out399, out _out400);
            r = _out399;
            resultingOwnership = _out400;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_SeqUpdate) {
          DAST._IExpression _1719_expr = _source76.dtor_expr;
          DAST._IExpression _1720_index = _source76.dtor_indexExpr;
          DAST._IExpression _1721_value = _source76.dtor_value;
          unmatched76 = false;
          {
            RAST._IExpr _1722_exprR;
            DCOMP._IOwnership _1723___v129;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1724_exprIdents;
            RAST._IExpr _out401;
            DCOMP._IOwnership _out402;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
            (this).GenExpr(_1719_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out401, out _out402, out _out403);
            _1722_exprR = _out401;
            _1723___v129 = _out402;
            _1724_exprIdents = _out403;
            RAST._IExpr _1725_indexR;
            DCOMP._IOwnership _1726_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1727_indexIdents;
            RAST._IExpr _out404;
            DCOMP._IOwnership _out405;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out406;
            (this).GenExpr(_1720_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out404, out _out405, out _out406);
            _1725_indexR = _out404;
            _1726_indexOwnership = _out405;
            _1727_indexIdents = _out406;
            RAST._IExpr _1728_valueR;
            DCOMP._IOwnership _1729_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1730_valueIdents;
            RAST._IExpr _out407;
            DCOMP._IOwnership _out408;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
            (this).GenExpr(_1721_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out407, out _out408, out _out409);
            _1728_valueR = _out407;
            _1729_valueOwnership = _out408;
            _1730_valueIdents = _out409;
            r = ((_1722_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1725_indexR, _1728_valueR));
            RAST._IExpr _out410;
            DCOMP._IOwnership _out411;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out410, out _out411);
            r = _out410;
            resultingOwnership = _out411;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1724_exprIdents, _1727_indexIdents), _1730_valueIdents);
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_MapUpdate) {
          DAST._IExpression _1731_expr = _source76.dtor_expr;
          DAST._IExpression _1732_index = _source76.dtor_indexExpr;
          DAST._IExpression _1733_value = _source76.dtor_value;
          unmatched76 = false;
          {
            RAST._IExpr _1734_exprR;
            DCOMP._IOwnership _1735___v130;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1736_exprIdents;
            RAST._IExpr _out412;
            DCOMP._IOwnership _out413;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out414;
            (this).GenExpr(_1731_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out412, out _out413, out _out414);
            _1734_exprR = _out412;
            _1735___v130 = _out413;
            _1736_exprIdents = _out414;
            RAST._IExpr _1737_indexR;
            DCOMP._IOwnership _1738_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1739_indexIdents;
            RAST._IExpr _out415;
            DCOMP._IOwnership _out416;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out417;
            (this).GenExpr(_1732_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out415, out _out416, out _out417);
            _1737_indexR = _out415;
            _1738_indexOwnership = _out416;
            _1739_indexIdents = _out417;
            RAST._IExpr _1740_valueR;
            DCOMP._IOwnership _1741_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1742_valueIdents;
            RAST._IExpr _out418;
            DCOMP._IOwnership _out419;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out420;
            (this).GenExpr(_1733_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out418, out _out419, out _out420);
            _1740_valueR = _out418;
            _1741_valueOwnership = _out419;
            _1742_valueIdents = _out420;
            r = ((_1734_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1737_indexR, _1740_valueR));
            RAST._IExpr _out421;
            DCOMP._IOwnership _out422;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out421, out _out422);
            r = _out421;
            resultingOwnership = _out422;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1736_exprIdents, _1739_indexIdents), _1742_valueIdents);
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_This) {
          unmatched76 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source77 = selfIdent;
            bool unmatched77 = true;
            if (unmatched77) {
              if (_source77.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1743_id = _source77.dtor_value;
                unmatched77 = false;
                {
                  r = RAST.Expr.create_Identifier(_1743_id);
                  if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
                    r = RAST.__default.Clone(r);
                    resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
                  } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
                    r = RAST.__default.BoxNew(RAST.__default.Clone(r));
                    resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
                  } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
                    if (!(_1743_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                      r = RAST.__default.Borrow(r);
                    }
                    resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
                  } else {
                    if (!(_1743_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                      r = RAST.__default.BorrowMut(r);
                    }
                    resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
                  }
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1743_id);
                }
              }
            }
            if (unmatched77) {
              unmatched77 = false;
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
      if (unmatched76) {
        if (_source76.is_Ite) {
          DAST._IExpression _1744_cond = _source76.dtor_cond;
          DAST._IExpression _1745_t = _source76.dtor_thn;
          DAST._IExpression _1746_f = _source76.dtor_els;
          unmatched76 = false;
          {
            RAST._IExpr _1747_cond;
            DCOMP._IOwnership _1748___v131;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1749_recIdentsCond;
            RAST._IExpr _out425;
            DCOMP._IOwnership _out426;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out427;
            (this).GenExpr(_1744_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out425, out _out426, out _out427);
            _1747_cond = _out425;
            _1748___v131 = _out426;
            _1749_recIdentsCond = _out427;
            Dafny.ISequence<Dafny.Rune> _1750_condString;
            _1750_condString = (_1747_cond)._ToString(DCOMP.__default.IND);
            RAST._IExpr _1751___v132;
            DCOMP._IOwnership _1752_tHasToBeOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1753___v133;
            RAST._IExpr _out428;
            DCOMP._IOwnership _out429;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out430;
            (this).GenExpr(_1745_t, selfIdent, env, expectedOwnership, out _out428, out _out429, out _out430);
            _1751___v132 = _out428;
            _1752_tHasToBeOwned = _out429;
            _1753___v133 = _out430;
            RAST._IExpr _1754_fExpr;
            DCOMP._IOwnership _1755_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1756_recIdentsF;
            RAST._IExpr _out431;
            DCOMP._IOwnership _out432;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out433;
            (this).GenExpr(_1746_f, selfIdent, env, _1752_tHasToBeOwned, out _out431, out _out432, out _out433);
            _1754_fExpr = _out431;
            _1755_fOwned = _out432;
            _1756_recIdentsF = _out433;
            Dafny.ISequence<Dafny.Rune> _1757_fString;
            _1757_fString = (_1754_fExpr)._ToString(DCOMP.__default.IND);
            RAST._IExpr _1758_tExpr;
            DCOMP._IOwnership _1759___v134;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1760_recIdentsT;
            RAST._IExpr _out434;
            DCOMP._IOwnership _out435;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out436;
            (this).GenExpr(_1745_t, selfIdent, env, _1755_fOwned, out _out434, out _out435, out _out436);
            _1758_tExpr = _out434;
            _1759___v134 = _out435;
            _1760_recIdentsT = _out436;
            Dafny.ISequence<Dafny.Rune> _1761_tString;
            _1761_tString = (_1758_tExpr)._ToString(DCOMP.__default.IND);
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _1750_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _1761_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _1757_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})")));
            RAST._IExpr _out437;
            DCOMP._IOwnership _out438;
            DCOMP.COMP.FromOwnership(r, _1755_fOwned, expectedOwnership, out _out437, out _out438);
            r = _out437;
            resultingOwnership = _out438;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1749_recIdentsCond, _1760_recIdentsT), _1756_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source76.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _1762_e = _source76.dtor_expr;
            DAST.Format._IUnaryOpFormat _1763_format = _source76.dtor_format1;
            unmatched76 = false;
            {
              RAST._IExpr _1764_recursiveGen;
              DCOMP._IOwnership _1765___v135;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1766_recIdents;
              RAST._IExpr _out439;
              DCOMP._IOwnership _out440;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out441;
              (this).GenExpr(_1762_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out439, out _out440, out _out441);
              _1764_recursiveGen = _out439;
              _1765___v135 = _out440;
              _1766_recIdents = _out441;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _1764_recursiveGen, _1763_format);
              RAST._IExpr _out442;
              DCOMP._IOwnership _out443;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out442, out _out443);
              r = _out442;
              resultingOwnership = _out443;
              readIdents = _1766_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source76.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _1767_e = _source76.dtor_expr;
            DAST.Format._IUnaryOpFormat _1768_format = _source76.dtor_format1;
            unmatched76 = false;
            {
              RAST._IExpr _1769_recursiveGen;
              DCOMP._IOwnership _1770___v136;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1771_recIdents;
              RAST._IExpr _out444;
              DCOMP._IOwnership _out445;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out446;
              (this).GenExpr(_1767_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out444, out _out445, out _out446);
              _1769_recursiveGen = _out444;
              _1770___v136 = _out445;
              _1771_recIdents = _out446;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _1769_recursiveGen, _1768_format);
              RAST._IExpr _out447;
              DCOMP._IOwnership _out448;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out447, out _out448);
              r = _out447;
              resultingOwnership = _out448;
              readIdents = _1771_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source76.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _1772_e = _source76.dtor_expr;
            DAST.Format._IUnaryOpFormat _1773_format = _source76.dtor_format1;
            unmatched76 = false;
            {
              RAST._IExpr _1774_recursiveGen;
              DCOMP._IOwnership _1775_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1776_recIdents;
              RAST._IExpr _out449;
              DCOMP._IOwnership _out450;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
              (this).GenExpr(_1772_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out449, out _out450, out _out451);
              _1774_recursiveGen = _out449;
              _1775_recOwned = _out450;
              _1776_recIdents = _out451;
              r = ((_1774_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out452;
              DCOMP._IOwnership _out453;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out452, out _out453);
              r = _out452;
              resultingOwnership = _out453;
              readIdents = _1776_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_BinOp) {
          DAST._IBinOp _1777___v137 = _source76.dtor_op;
          DAST._IExpression _1778___v138 = _source76.dtor_left;
          DAST._IExpression _1779___v139 = _source76.dtor_right;
          DAST.Format._IBinaryOpFormat _1780___v140 = _source76.dtor_format2;
          unmatched76 = false;
          RAST._IExpr _out454;
          DCOMP._IOwnership _out455;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out456;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out454, out _out455, out _out456);
          r = _out454;
          resultingOwnership = _out455;
          readIdents = _out456;
        }
      }
      if (unmatched76) {
        if (_source76.is_ArrayLen) {
          DAST._IExpression _1781_expr = _source76.dtor_expr;
          BigInteger _1782_dim = _source76.dtor_dim;
          unmatched76 = false;
          {
            RAST._IExpr _1783_recursiveGen;
            DCOMP._IOwnership _1784___v141;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1785_recIdents;
            RAST._IExpr _out457;
            DCOMP._IOwnership _out458;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out459;
            (this).GenExpr(_1781_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out457, out _out458, out _out459);
            _1783_recursiveGen = _out457;
            _1784___v141 = _out458;
            _1785_recIdents = _out459;
            if ((_1782_dim).Sign == 0) {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), (_1783_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())")));
            } else {
              Dafny.ISequence<Dafny.Rune> _1786_s;
              _1786_s = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(m.borrow().len())")))._ToString(DCOMP.__default.IND);
              BigInteger _1787_i;
              _1787_i = BigInteger.One;
              while ((_1787_i) < (_1782_dim)) {
                _1786_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("m.borrow().get(0).map(|m| "), _1786_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"));
                _1787_i = (_1787_i) + (BigInteger.One);
              }
              r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_1783_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow().get(0).map(|m| ")), _1786_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"))));
            }
            RAST._IExpr _out460;
            DCOMP._IOwnership _out461;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out460, out _out461);
            r = _out460;
            resultingOwnership = _out461;
            readIdents = _1785_recIdents;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_MapKeys) {
          DAST._IExpression _1788_expr = _source76.dtor_expr;
          unmatched76 = false;
          {
            RAST._IExpr _1789_recursiveGen;
            DCOMP._IOwnership _1790___v142;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1791_recIdents;
            RAST._IExpr _out462;
            DCOMP._IOwnership _out463;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out464;
            (this).GenExpr(_1788_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out462, out _out463, out _out464);
            _1789_recursiveGen = _out462;
            _1790___v142 = _out463;
            _1791_recIdents = _out464;
            readIdents = _1791_recIdents;
            r = ((_1789_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out465;
            DCOMP._IOwnership _out466;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out465, out _out466);
            r = _out465;
            resultingOwnership = _out466;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_MapValues) {
          DAST._IExpression _1792_expr = _source76.dtor_expr;
          unmatched76 = false;
          {
            RAST._IExpr _1793_recursiveGen;
            DCOMP._IOwnership _1794___v143;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1795_recIdents;
            RAST._IExpr _out467;
            DCOMP._IOwnership _out468;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out469;
            (this).GenExpr(_1792_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out467, out _out468, out _out469);
            _1793_recursiveGen = _out467;
            _1794___v143 = _out468;
            _1795_recIdents = _out469;
            readIdents = _1795_recIdents;
            r = ((_1793_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out470;
            DCOMP._IOwnership _out471;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out470, out _out471);
            r = _out470;
            resultingOwnership = _out471;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_SelectFn) {
          DAST._IExpression _1796_on = _source76.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1797_field = _source76.dtor_field;
          bool _1798_isDatatype = _source76.dtor_onDatatype;
          bool _1799_isStatic = _source76.dtor_isStatic;
          BigInteger _1800_arity = _source76.dtor_arity;
          unmatched76 = false;
          {
            RAST._IExpr _1801_onExpr;
            DCOMP._IOwnership _1802_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1803_recIdents;
            RAST._IExpr _out472;
            DCOMP._IOwnership _out473;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out474;
            (this).GenExpr(_1796_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out472, out _out473, out _out474);
            _1801_onExpr = _out472;
            _1802_onOwned = _out473;
            _1803_recIdents = _out474;
            Dafny.ISequence<Dafny.Rune> _1804_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _1805_onString;
            _1805_onString = (_1801_onExpr)._ToString(DCOMP.__default.IND);
            if (_1799_isStatic) {
              _1804_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1805_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_1797_field));
            } else {
              _1804_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _1804_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1804_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _1805_onString), ((object.Equals(_1802_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _1806_args;
              _1806_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _1807_i;
              _1807_i = BigInteger.Zero;
              while ((_1807_i) < (_1800_arity)) {
                if ((_1807_i).Sign == 1) {
                  _1806_args = Dafny.Sequence<Dafny.Rune>.Concat(_1806_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _1806_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1806_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_1807_i));
                _1807_i = (_1807_i) + (BigInteger.One);
              }
              _1804_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1804_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _1806_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _1804_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1804_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_1797_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1806_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _1804_s = Dafny.Sequence<Dafny.Rune>.Concat(_1804_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _1804_s = Dafny.Sequence<Dafny.Rune>.Concat(_1804_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _1808_typeShape;
            _1808_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _1809_i;
            _1809_i = BigInteger.Zero;
            while ((_1809_i) < (_1800_arity)) {
              if ((_1809_i).Sign == 1) {
                _1808_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1808_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _1808_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1808_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _1809_i = (_1809_i) + (BigInteger.One);
            }
            _1808_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1808_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _1804_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _1804_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _1808_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_1804_s);
            RAST._IExpr _out475;
            DCOMP._IOwnership _out476;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out475, out _out476);
            r = _out475;
            resultingOwnership = _out476;
            readIdents = _1803_recIdents;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Select) {
          DAST._IExpression expr0 = _source76.dtor_expr;
          if (expr0.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1810_c = expr0.dtor_Companion_a0;
            Dafny.ISequence<Dafny.Rune> _1811_field = _source76.dtor_field;
            bool _1812_isConstant = _source76.dtor_isConstant;
            bool _1813_isDatatype = _source76.dtor_onDatatype;
            DAST._IType _1814_fieldType = _source76.dtor_fieldType;
            unmatched76 = false;
            {
              RAST._IExpr _1815_onExpr;
              DCOMP._IOwnership _1816_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1817_recIdents;
              RAST._IExpr _out477;
              DCOMP._IOwnership _out478;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out479;
              (this).GenExpr(DAST.Expression.create_Companion(_1810_c), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out477, out _out478, out _out479);
              _1815_onExpr = _out477;
              _1816_onOwned = _out478;
              _1817_recIdents = _out479;
              r = ((_1815_onExpr).MSel(DCOMP.__default.escapeName(_1811_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out480;
              DCOMP._IOwnership _out481;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out480, out _out481);
              r = _out480;
              resultingOwnership = _out481;
              readIdents = _1817_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Select) {
          DAST._IExpression _1818_on = _source76.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1819_field = _source76.dtor_field;
          bool _1820_isConstant = _source76.dtor_isConstant;
          bool _1821_isDatatype = _source76.dtor_onDatatype;
          DAST._IType _1822_fieldType = _source76.dtor_fieldType;
          unmatched76 = false;
          {
            if (_1821_isDatatype) {
              RAST._IExpr _1823_onExpr;
              DCOMP._IOwnership _1824_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1825_recIdents;
              RAST._IExpr _out482;
              DCOMP._IOwnership _out483;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out484;
              (this).GenExpr(_1818_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out482, out _out483, out _out484);
              _1823_onExpr = _out482;
              _1824_onOwned = _out483;
              _1825_recIdents = _out484;
              r = ((_1823_onExpr).Sel(DCOMP.__default.escapeName(_1819_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _1826_typ;
              RAST._IType _out485;
              _out485 = (this).GenType(_1822_fieldType, false, false);
              _1826_typ = _out485;
              RAST._IExpr _out486;
              DCOMP._IOwnership _out487;
              DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out486, out _out487);
              r = _out486;
              resultingOwnership = _out487;
              readIdents = _1825_recIdents;
            } else {
              RAST._IExpr _1827_onExpr;
              DCOMP._IOwnership _1828_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1829_recIdents;
              RAST._IExpr _out488;
              DCOMP._IOwnership _out489;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out490;
              (this).GenExpr(_1818_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out488, out _out489, out _out490);
              _1827_onExpr = _out488;
              _1828_onOwned = _out489;
              _1829_recIdents = _out490;
              r = _1827_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_1819_field));
              if (_1820_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _1830_s;
                _1830_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_1827_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_1819_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_1830_s);
              }
              DCOMP._IOwnership _1831_fromOwnership;
              _1831_fromOwnership = ((_1820_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out491;
              DCOMP._IOwnership _out492;
              DCOMP.COMP.FromOwnership(r, _1831_fromOwnership, expectedOwnership, out _out491, out _out492);
              r = _out491;
              resultingOwnership = _out492;
              readIdents = _1829_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Index) {
          DAST._IExpression _1832_on = _source76.dtor_expr;
          DAST._ICollKind _1833_collKind = _source76.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _1834_indices = _source76.dtor_indices;
          unmatched76 = false;
          {
            RAST._IExpr _1835_onExpr;
            DCOMP._IOwnership _1836_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1837_recIdents;
            RAST._IExpr _out493;
            DCOMP._IOwnership _out494;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out495;
            (this).GenExpr(_1832_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out493, out _out494, out _out495);
            _1835_onExpr = _out493;
            _1836_onOwned = _out494;
            _1837_recIdents = _out495;
            readIdents = _1837_recIdents;
            r = _1835_onExpr;
            BigInteger _1838_i;
            _1838_i = BigInteger.Zero;
            while ((_1838_i) < (new BigInteger((_1834_indices).Count))) {
              if (object.Equals(_1833_collKind, DAST.CollKind.create_Array())) {
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              RAST._IExpr _1839_idx;
              DCOMP._IOwnership _1840_idxOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1841_recIdentsIdx;
              RAST._IExpr _out496;
              DCOMP._IOwnership _out497;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out498;
              (this).GenExpr((_1834_indices).Select(_1838_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out496, out _out497, out _out498);
              _1839_idx = _out496;
              _1840_idxOwned = _out497;
              _1841_recIdentsIdx = _out498;
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_1839_idx);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1841_recIdentsIdx);
              _1838_i = (_1838_i) + (BigInteger.One);
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
      if (unmatched76) {
        if (_source76.is_IndexRange) {
          DAST._IExpression _1842_on = _source76.dtor_expr;
          bool _1843_isArray = _source76.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _1844_low = _source76.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _1845_high = _source76.dtor_high;
          unmatched76 = false;
          {
            RAST._IExpr _1846_onExpr;
            DCOMP._IOwnership _1847_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1848_recIdents;
            RAST._IExpr _out501;
            DCOMP._IOwnership _out502;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out503;
            (this).GenExpr(_1842_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out501, out _out502, out _out503);
            _1846_onExpr = _out501;
            _1847_onOwned = _out502;
            _1848_recIdents = _out503;
            readIdents = _1848_recIdents;
            Dafny.ISequence<Dafny.Rune> _1849_methodName;
            _1849_methodName = (((_1844_low).is_Some) ? ((((_1845_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_1845_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _1850_arguments;
            _1850_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source78 = _1844_low;
            bool unmatched78 = true;
            if (unmatched78) {
              if (_source78.is_Some) {
                DAST._IExpression _1851_l = _source78.dtor_value;
                unmatched78 = false;
                {
                  RAST._IExpr _1852_lExpr;
                  DCOMP._IOwnership _1853___v144;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1854_recIdentsL;
                  RAST._IExpr _out504;
                  DCOMP._IOwnership _out505;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out506;
                  (this).GenExpr(_1851_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out504, out _out505, out _out506);
                  _1852_lExpr = _out504;
                  _1853___v144 = _out505;
                  _1854_recIdentsL = _out506;
                  _1850_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1850_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1852_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1854_recIdentsL);
                }
              }
            }
            if (unmatched78) {
              unmatched78 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source79 = _1845_high;
            bool unmatched79 = true;
            if (unmatched79) {
              if (_source79.is_Some) {
                DAST._IExpression _1855_h = _source79.dtor_value;
                unmatched79 = false;
                {
                  RAST._IExpr _1856_hExpr;
                  DCOMP._IOwnership _1857___v145;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1858_recIdentsH;
                  RAST._IExpr _out507;
                  DCOMP._IOwnership _out508;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out509;
                  (this).GenExpr(_1855_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out507, out _out508, out _out509);
                  _1856_hExpr = _out507;
                  _1857___v145 = _out508;
                  _1858_recIdentsH = _out509;
                  _1850_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1850_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1856_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1858_recIdentsH);
                }
              }
            }
            if (unmatched79) {
              unmatched79 = false;
            }
            r = _1846_onExpr;
            if (_1843_isArray) {
              if (!(_1849_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _1849_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1849_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _1849_methodName))).Apply(_1850_arguments);
            } else {
              if (!(_1849_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_1849_methodName)).Apply(_1850_arguments);
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
      if (unmatched76) {
        if (_source76.is_TupleSelect) {
          DAST._IExpression _1859_on = _source76.dtor_expr;
          BigInteger _1860_idx = _source76.dtor_index;
          DAST._IType _1861_fieldType = _source76.dtor_fieldType;
          unmatched76 = false;
          {
            RAST._IExpr _1862_onExpr;
            DCOMP._IOwnership _1863_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1864_recIdents;
            RAST._IExpr _out512;
            DCOMP._IOwnership _out513;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out514;
            (this).GenExpr(_1859_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out512, out _out513, out _out514);
            _1862_onExpr = _out512;
            _1863_onOwnership = _out513;
            _1864_recIdents = _out514;
            Dafny.ISequence<Dafny.Rune> _1865_selName;
            _1865_selName = Std.Strings.__default.OfNat(_1860_idx);
            DAST._IType _source80 = _1861_fieldType;
            bool unmatched80 = true;
            if (unmatched80) {
              if (_source80.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1866_tps = _source80.dtor_Tuple_a0;
                unmatched80 = false;
                if (((_1861_fieldType).is_Tuple) && ((new BigInteger((_1866_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _1865_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1865_selName);
                }
              }
            }
            if (unmatched80) {
              DAST._IType _1867___v146 = _source80;
              unmatched80 = false;
            }
            r = (_1862_onExpr).Sel(_1865_selName);
            RAST._IExpr _out515;
            DCOMP._IOwnership _out516;
            DCOMP.COMP.FromOwnership(r, _1863_onOwnership, expectedOwnership, out _out515, out _out516);
            r = _out515;
            resultingOwnership = _out516;
            readIdents = _1864_recIdents;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Call) {
          DAST._IExpression _1868_on = _source76.dtor_on;
          DAST._ICallName _1869_name = _source76.dtor_callName;
          Dafny.ISequence<DAST._IType> _1870_typeArgs = _source76.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1871_args = _source76.dtor_args;
          unmatched76 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IExpr _1872_onExpr;
            DCOMP._IOwnership _1873___v147;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1874_recIdents;
            RAST._IExpr _out517;
            DCOMP._IOwnership _out518;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out519;
            (this).GenExpr(_1868_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out517, out _out518, out _out519);
            _1872_onExpr = _out517;
            _1873___v147 = _out518;
            _1874_recIdents = _out519;
            Dafny.ISequence<RAST._IType> _1875_typeExprs;
            _1875_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
            if ((new BigInteger((_1870_typeArgs).Count)) >= (BigInteger.One)) {
              BigInteger _hi35 = new BigInteger((_1870_typeArgs).Count);
              for (BigInteger _1876_typeI = BigInteger.Zero; _1876_typeI < _hi35; _1876_typeI++) {
                RAST._IType _1877_typeExpr;
                RAST._IType _out520;
                _out520 = (this).GenType((_1870_typeArgs).Select(_1876_typeI), false, false);
                _1877_typeExpr = _out520;
                _1875_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1875_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1877_typeExpr));
              }
            }
            Dafny.ISequence<RAST._IExpr> _1878_argExprs;
            _1878_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi36 = new BigInteger((_1871_args).Count);
            for (BigInteger _1879_i = BigInteger.Zero; _1879_i < _hi36; _1879_i++) {
              DCOMP._IOwnership _1880_argOwnership;
              _1880_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              if (((_1869_name).is_CallName) && ((_1879_i) < (new BigInteger((((_1869_name).dtor_signature)).Count)))) {
                RAST._IType _1881_tpe;
                RAST._IType _out521;
                _out521 = (this).GenType(((((_1869_name).dtor_signature)).Select(_1879_i)).dtor_typ, false, false);
                _1881_tpe = _out521;
                if ((_1881_tpe).CanReadWithoutClone()) {
                  _1880_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
                }
              }
              RAST._IExpr _1882_argExpr;
              DCOMP._IOwnership _1883___v148;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1884_argIdents;
              RAST._IExpr _out522;
              DCOMP._IOwnership _out523;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out524;
              (this).GenExpr((_1871_args).Select(_1879_i), selfIdent, env, _1880_argOwnership, out _out522, out _out523, out _out524);
              _1882_argExpr = _out522;
              _1883___v148 = _out523;
              _1884_argIdents = _out524;
              _1878_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1878_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1882_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1884_argIdents);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1874_recIdents);
            Dafny.ISequence<Dafny.Rune> _1885_renderedName;
            _1885_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
              DAST._ICallName _source81 = _1869_name;
              bool unmatched81 = true;
              if (unmatched81) {
                if (_source81.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _1886_ident = _source81.dtor_name;
                  Std.Wrappers._IOption<DAST._IType> _1887___v149 = _source81.dtor_onType;
                  Dafny.ISequence<DAST._IFormal> _1888___v150 = _source81.dtor_signature;
                  unmatched81 = false;
                  return DCOMP.__default.escapeName(_1886_ident);
                }
              }
              if (unmatched81) {
                bool disjunctiveMatch12 = false;
                if (_source81.is_MapBuilderAdd) {
                  disjunctiveMatch12 = true;
                }
                if (_source81.is_SetBuilderAdd) {
                  disjunctiveMatch12 = true;
                }
                if (disjunctiveMatch12) {
                  unmatched81 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                }
              }
              if (unmatched81) {
                bool disjunctiveMatch13 = false;
                disjunctiveMatch13 = true;
                disjunctiveMatch13 = true;
                if (disjunctiveMatch13) {
                  unmatched81 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                }
              }
              throw new System.Exception("unexpected control point");
            }))();
            DAST._IExpression _source82 = _1868_on;
            bool unmatched82 = true;
            if (unmatched82) {
              if (_source82.is_Companion) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1889___v151 = _source82.dtor_Companion_a0;
                unmatched82 = false;
                {
                  _1872_onExpr = (_1872_onExpr).MSel(_1885_renderedName);
                }
              }
            }
            if (unmatched82) {
              DAST._IExpression _1890___v152 = _source82;
              unmatched82 = false;
              {
                _1872_onExpr = (_1872_onExpr).Sel(_1885_renderedName);
              }
            }
            r = _1872_onExpr;
            if ((new BigInteger((_1875_typeExprs).Count)).Sign == 1) {
              r = (r).ApplyType(_1875_typeExprs);
            }
            r = (r).Apply(_1878_argExprs);
            RAST._IExpr _out525;
            DCOMP._IOwnership _out526;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out525, out _out526);
            r = _out525;
            resultingOwnership = _out526;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _1891_paramsDafny = _source76.dtor_params;
          DAST._IType _1892_retType = _source76.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _1893_body = _source76.dtor_body;
          unmatched76 = false;
          {
            Dafny.ISequence<RAST._IFormal> _1894_params;
            Dafny.ISequence<RAST._IFormal> _out527;
            _out527 = (this).GenParams(_1891_paramsDafny);
            _1894_params = _out527;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1895_paramNames;
            _1895_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1896_paramTypesMap;
            _1896_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi37 = new BigInteger((_1894_params).Count);
            for (BigInteger _1897_i = BigInteger.Zero; _1897_i < _hi37; _1897_i++) {
              Dafny.ISequence<Dafny.Rune> _1898_name;
              _1898_name = ((_1894_params).Select(_1897_i)).dtor_name;
              _1895_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1895_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1898_name));
              _1896_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1896_paramTypesMap, _1898_name, ((_1894_params).Select(_1897_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _1899_env;
            _1899_env = DCOMP.Environment.create(_1895_paramNames, _1896_paramTypesMap);
            RAST._IExpr _1900_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1901_recIdents;
            DCOMP._IEnvironment _1902___v153;
            RAST._IExpr _out528;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out529;
            DCOMP._IEnvironment _out530;
            (this).GenStmts(_1893_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), _1899_env, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out528, out _out529, out _out530);
            _1900_recursiveGen = _out528;
            _1901_recIdents = _out529;
            _1902___v153 = _out530;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _1901_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1901_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_1903_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll6 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in (_1903_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _1904_name = (Dafny.ISequence<Dafny.Rune>)_compr_6;
                if ((_1903_paramNames).Contains(_1904_name)) {
                  _coll6.Add(_1904_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll6);
            }))())(_1895_paramNames));
            RAST._IExpr _1905_allReadCloned;
            _1905_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_1901_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _1906_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_1901_recIdents).Elements) {
                _1906_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_1901_recIdents).Contains(_1906_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 3810)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) && ((_1906_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
                  _1905_allReadCloned = (_1905_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
                }
              } else if (!((_1895_paramNames).Contains(_1906_next))) {
                _1905_allReadCloned = (_1905_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1906_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.Expr.create_Identifier(_1906_next)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1906_next));
              }
              _1901_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1901_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1906_next));
            }
            RAST._IType _1907_retTypeGen;
            RAST._IType _out531;
            _out531 = (this).GenType(_1892_retType, false, true);
            _1907_retTypeGen = _out531;
            r = RAST.Expr.create_Block((_1905_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_1894_params, Std.Wrappers.Option<RAST._IType>.create_Some(_1907_retTypeGen), RAST.Expr.create_Block(_1900_recursiveGen)))));
            RAST._IExpr _out532;
            DCOMP._IOwnership _out533;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out532, out _out533);
            r = _out532;
            resultingOwnership = _out533;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _1908_values = _source76.dtor_values;
          DAST._IType _1909_retType = _source76.dtor_retType;
          DAST._IExpression _1910_expr = _source76.dtor_expr;
          unmatched76 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1911_paramNames;
            _1911_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _1912_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out534;
            _out534 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_1913_value) => {
              return (_1913_value).dtor__0;
            })), _1908_values));
            _1912_paramFormals = _out534;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1914_paramTypes;
            _1914_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1915_paramNamesSet;
            _1915_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi38 = new BigInteger((_1908_values).Count);
            for (BigInteger _1916_i = BigInteger.Zero; _1916_i < _hi38; _1916_i++) {
              Dafny.ISequence<Dafny.Rune> _1917_name;
              _1917_name = (((_1908_values).Select(_1916_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _1918_rName;
              _1918_rName = DCOMP.__default.escapeName(_1917_name);
              _1911_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1911_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1918_rName));
              _1914_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1914_paramTypes, _1918_rName, ((_1912_paramFormals).Select(_1916_i)).dtor_tpe);
              _1915_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1915_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1918_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi39 = new BigInteger((_1908_values).Count);
            for (BigInteger _1919_i = BigInteger.Zero; _1919_i < _hi39; _1919_i++) {
              RAST._IType _1920_typeGen;
              RAST._IType _out535;
              _out535 = (this).GenType((((_1908_values).Select(_1919_i)).dtor__0).dtor_typ, false, true);
              _1920_typeGen = _out535;
              RAST._IExpr _1921_valueGen;
              DCOMP._IOwnership _1922___v154;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1923_recIdents;
              RAST._IExpr _out536;
              DCOMP._IOwnership _out537;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out538;
              (this).GenExpr(((_1908_values).Select(_1919_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out536, out _out537, out _out538);
              _1921_valueGen = _out536;
              _1922___v154 = _out537;
              _1923_recIdents = _out538;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_1908_values).Select(_1919_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1920_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1921_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1923_recIdents);
            }
            DCOMP._IEnvironment _1924_newEnv;
            _1924_newEnv = DCOMP.Environment.create(_1911_paramNames, _1914_paramTypes);
            RAST._IExpr _1925_recGen;
            DCOMP._IOwnership _1926_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1927_recIdents;
            RAST._IExpr _out539;
            DCOMP._IOwnership _out540;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
            (this).GenExpr(_1910_expr, selfIdent, _1924_newEnv, expectedOwnership, out _out539, out _out540, out _out541);
            _1925_recGen = _out539;
            _1926_recOwned = _out540;
            _1927_recIdents = _out541;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1927_recIdents, _1915_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_1925_recGen));
            RAST._IExpr _out542;
            DCOMP._IOwnership _out543;
            DCOMP.COMP.FromOwnership(r, _1926_recOwned, expectedOwnership, out _out542, out _out543);
            r = _out542;
            resultingOwnership = _out543;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _1928_name = _source76.dtor_name;
          DAST._IType _1929_tpe = _source76.dtor_typ;
          DAST._IExpression _1930_value = _source76.dtor_value;
          DAST._IExpression _1931_iifeBody = _source76.dtor_iifeBody;
          unmatched76 = false;
          {
            RAST._IExpr _1932_valueGen;
            DCOMP._IOwnership _1933___v155;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1934_recIdents;
            RAST._IExpr _out544;
            DCOMP._IOwnership _out545;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out546;
            (this).GenExpr(_1930_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out544, out _out545, out _out546);
            _1932_valueGen = _out544;
            _1933___v155 = _out545;
            _1934_recIdents = _out546;
            readIdents = _1934_recIdents;
            RAST._IType _1935_valueTypeGen;
            RAST._IType _out547;
            _out547 = (this).GenType(_1929_tpe, false, true);
            _1935_valueTypeGen = _out547;
            RAST._IExpr _1936_bodyGen;
            DCOMP._IOwnership _1937___v156;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1938_bodyIdents;
            RAST._IExpr _out548;
            DCOMP._IOwnership _out549;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out550;
            (this).GenExpr(_1931_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out548, out _out549, out _out550);
            _1936_bodyGen = _out548;
            _1937___v156 = _out549;
            _1938_bodyIdents = _out550;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1938_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_1928_name)))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_1928_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_1935_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1932_valueGen))).Then(_1936_bodyGen));
            RAST._IExpr _out551;
            DCOMP._IOwnership _out552;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out551, out _out552);
            r = _out551;
            resultingOwnership = _out552;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Apply) {
          DAST._IExpression _1939_func = _source76.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _1940_args = _source76.dtor_args;
          unmatched76 = false;
          {
            RAST._IExpr _1941_funcExpr;
            DCOMP._IOwnership _1942___v157;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1943_recIdents;
            RAST._IExpr _out553;
            DCOMP._IOwnership _out554;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out555;
            (this).GenExpr(_1939_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out553, out _out554, out _out555);
            _1941_funcExpr = _out553;
            _1942___v157 = _out554;
            _1943_recIdents = _out555;
            readIdents = _1943_recIdents;
            Dafny.ISequence<RAST._IExpr> _1944_rArgs;
            _1944_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi40 = new BigInteger((_1940_args).Count);
            for (BigInteger _1945_i = BigInteger.Zero; _1945_i < _hi40; _1945_i++) {
              RAST._IExpr _1946_argExpr;
              DCOMP._IOwnership _1947_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1948_argIdents;
              RAST._IExpr _out556;
              DCOMP._IOwnership _out557;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out558;
              (this).GenExpr((_1940_args).Select(_1945_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out556, out _out557, out _out558);
              _1946_argExpr = _out556;
              _1947_argOwned = _out557;
              _1948_argIdents = _out558;
              _1944_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1944_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1946_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1948_argIdents);
            }
            r = (_1941_funcExpr).Apply(_1944_rArgs);
            RAST._IExpr _out559;
            DCOMP._IOwnership _out560;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out559, out _out560);
            r = _out559;
            resultingOwnership = _out560;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_TypeTest) {
          DAST._IExpression _1949_on = _source76.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1950_dType = _source76.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _1951_variant = _source76.dtor_variant;
          unmatched76 = false;
          {
            RAST._IExpr _1952_exprGen;
            DCOMP._IOwnership _1953___v158;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1954_recIdents;
            RAST._IExpr _out561;
            DCOMP._IOwnership _out562;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out563;
            (this).GenExpr(_1949_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out561, out _out562, out _out563);
            _1952_exprGen = _out561;
            _1953___v158 = _out562;
            _1954_recIdents = _out563;
            RAST._IType _1955_dTypePath;
            RAST._IType _out564;
            _out564 = DCOMP.COMP.GenPath(_1950_dType);
            _1955_dTypePath = _out564;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_1952_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_1955_dTypePath).MSel(DCOMP.__default.escapeName(_1951_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out565;
            DCOMP._IOwnership _out566;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out565, out _out566);
            r = _out565;
            resultingOwnership = _out566;
            readIdents = _1954_recIdents;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_BoolBoundedPool) {
          unmatched76 = false;
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
      if (unmatched76) {
        if (_source76.is_SetBoundedPool) {
          DAST._IExpression _1956_of = _source76.dtor_of;
          unmatched76 = false;
          {
            RAST._IExpr _1957_exprGen;
            DCOMP._IOwnership _1958___v159;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1959_recIdents;
            RAST._IExpr _out569;
            DCOMP._IOwnership _out570;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out571;
            (this).GenExpr(_1956_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out569, out _out570, out _out571);
            _1957_exprGen = _out569;
            _1958___v159 = _out570;
            _1959_recIdents = _out571;
            r = ((((_1957_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out572;
            DCOMP._IOwnership _out573;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out572, out _out573);
            r = _out572;
            resultingOwnership = _out573;
            readIdents = _1959_recIdents;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_SeqBoundedPool) {
          DAST._IExpression _1960_of = _source76.dtor_of;
          bool _1961_includeDuplicates = _source76.dtor_includeDuplicates;
          unmatched76 = false;
          {
            RAST._IExpr _1962_exprGen;
            DCOMP._IOwnership _1963___v160;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1964_recIdents;
            RAST._IExpr _out574;
            DCOMP._IOwnership _out575;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out576;
            (this).GenExpr(_1960_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out574, out _out575, out _out576);
            _1962_exprGen = _out574;
            _1963___v160 = _out575;
            _1964_recIdents = _out576;
            r = ((_1962_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_1961_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out577;
            DCOMP._IOwnership _out578;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out577, out _out578);
            r = _out577;
            resultingOwnership = _out578;
            readIdents = _1964_recIdents;
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_IntRange) {
          DAST._IExpression _1965_lo = _source76.dtor_lo;
          DAST._IExpression _1966_hi = _source76.dtor_hi;
          unmatched76 = false;
          {
            RAST._IExpr _1967_lo;
            DCOMP._IOwnership _1968___v161;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1969_recIdentsLo;
            RAST._IExpr _out579;
            DCOMP._IOwnership _out580;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out581;
            (this).GenExpr(_1965_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out579, out _out580, out _out581);
            _1967_lo = _out579;
            _1968___v161 = _out580;
            _1969_recIdentsLo = _out581;
            RAST._IExpr _1970_hi;
            DCOMP._IOwnership _1971___v162;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1972_recIdentsHi;
            RAST._IExpr _out582;
            DCOMP._IOwnership _out583;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out584;
            (this).GenExpr(_1966_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out582, out _out583, out _out584);
            _1970_hi = _out582;
            _1971___v162 = _out583;
            _1972_recIdentsHi = _out584;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1967_lo, _1970_hi));
            RAST._IExpr _out585;
            DCOMP._IOwnership _out586;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out585, out _out586);
            r = _out585;
            resultingOwnership = _out586;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1969_recIdentsLo, _1972_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_MapBuilder) {
          DAST._IType _1973_keyType = _source76.dtor_keyType;
          DAST._IType _1974_valueType = _source76.dtor_valueType;
          unmatched76 = false;
          {
            RAST._IType _1975_kType;
            RAST._IType _out587;
            _out587 = (this).GenType(_1973_keyType, false, false);
            _1975_kType = _out587;
            RAST._IType _1976_vType;
            RAST._IType _out588;
            _out588 = (this).GenType(_1974_valueType, false, false);
            _1976_vType = _out588;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1975_kType, _1976_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
      if (unmatched76) {
        DAST._IType _1977_elemType = _source76.dtor_elemType;
        unmatched76 = false;
        {
          RAST._IType _1978_eType;
          RAST._IType _out591;
          _out591 = (this).GenType(_1977_elemType, false, false);
          _1978_eType = _out591;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1978_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out592;
          DCOMP._IOwnership _out593;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out592, out _out593);
          r = _out592;
          resultingOwnership = _out593;
          return ;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      BigInteger _1979_i;
      _1979_i = BigInteger.Zero;
      while ((_1979_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _1980_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _1981_m;
        RAST._IMod _out594;
        _out594 = (this).GenModule((p).Select(_1979_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _1981_m = _out594;
        _1980_generated = (_1981_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_1979_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _1980_generated);
        _1979_i = (_1979_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _1982_i;
      _1982_i = BigInteger.Zero;
      while ((_1982_i) < (new BigInteger((fullName).Count))) {
        if ((_1982_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_1982_i)));
        _1982_i = (_1982_i) + (BigInteger.One);
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