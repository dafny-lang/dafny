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
          DAST._IDatatype _1051_d = _source44.dtor_Datatype_a0;
          unmatched44 = false;
          Dafny.ISequence<RAST._IModDecl> _out20;
          _out20 = (this).GenDatatype(_1051_d);
          _1044_generated = _out20;
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
      Dafny.ISequence<RAST._IType> _1052_genTpConstraint;
      _1052_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1052_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1052_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1052_genTpConstraint);
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
        for (BigInteger _1053_tpI = BigInteger.Zero; _1053_tpI < _hi6; _1053_tpI++) {
          DAST._ITypeArgDecl _1054_tp;
          _1054_tp = (@params).Select(_1053_tpI);
          DAST._IType _1055_typeArg;
          RAST._ITypeParamDecl _1056_typeParam;
          DAST._IType _out21;
          RAST._ITypeParamDecl _out22;
          (this).GenTypeParam(_1054_tp, out _out21, out _out22);
          _1055_typeArg = _out21;
          _1056_typeParam = _out22;
          RAST._IType _1057_rType;
          RAST._IType _out23;
          _out23 = (this).GenType(_1055_typeArg, false, false);
          _1057_rType = _out23;
          typeParamsSet = Dafny.Set<DAST._IType>.Union(typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1055_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1057_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1056_typeParam));
        }
      }
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1058_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1059_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1060_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1061_whereConstraints;
      Dafny.ISet<DAST._IType> _out24;
      Dafny.ISequence<RAST._IType> _out25;
      Dafny.ISequence<RAST._ITypeParamDecl> _out26;
      Dafny.ISequence<Dafny.Rune> _out27;
      (this).GenTypeParameters((c).dtor_typeParams, out _out24, out _out25, out _out26, out _out27);
      _1058_typeParamsSet = _out24;
      _1059_rTypeParams = _out25;
      _1060_rTypeParamsDecls = _out26;
      _1061_whereConstraints = _out27;
      Dafny.ISequence<Dafny.Rune> _1062_constrainedTypeParams;
      _1062_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1060_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1063_fields;
      _1063_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1064_fieldInits;
      _1064_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1065_fieldI = BigInteger.Zero; _1065_fieldI < _hi7; _1065_fieldI++) {
        DAST._IField _1066_field;
        _1066_field = ((c).dtor_fields).Select(_1065_fieldI);
        RAST._IType _1067_fieldType;
        RAST._IType _out28;
        _out28 = (this).GenType(((_1066_field).dtor_formal).dtor_typ, false, false);
        _1067_fieldType = _out28;
        Dafny.ISequence<Dafny.Rune> _1068_fieldRustName;
        _1068_fieldRustName = DCOMP.__default.escapeName(((_1066_field).dtor_formal).dtor_name);
        _1063_fields = Dafny.Sequence<RAST._IField>.Concat(_1063_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1068_fieldRustName, _1067_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source45 = (_1066_field).dtor_defaultValue;
        bool unmatched45 = true;
        if (unmatched45) {
          if (_source45.is_Some) {
            DAST._IExpression _1069_e = _source45.dtor_value;
            unmatched45 = false;
            {
              RAST._IExpr _1070_expr;
              DCOMP._IOwnership _1071___v42;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1072___v43;
              RAST._IExpr _out29;
              DCOMP._IOwnership _out30;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out31;
              (this).GenExpr(_1069_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out29, out _out30, out _out31);
              _1070_expr = _out29;
              _1071___v42 = _out30;
              _1072___v43 = _out31;
              _1064_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1064_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1066_field).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cell::RefCell::new("), (_1070_expr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))))));
            }
          }
        }
        if (unmatched45) {
          unmatched45 = false;
          {
            RAST._IExpr _1073_default;
            _1073_default = RAST.__default.std__Default__default;
            _1064_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1064_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1068_fieldRustName, _1073_default)));
          }
        }
      }
      BigInteger _hi8 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1074_typeParamI = BigInteger.Zero; _1074_typeParamI < _hi8; _1074_typeParamI++) {
        DAST._IType _1075_typeArg;
        RAST._ITypeParamDecl _1076_typeParam;
        DAST._IType _out32;
        RAST._ITypeParamDecl _out33;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1074_typeParamI), out _out32, out _out33);
        _1075_typeArg = _out32;
        _1076_typeParam = _out33;
        RAST._IType _1077_rTypeArg;
        RAST._IType _out34;
        _out34 = (this).GenType(_1075_typeArg, false, false);
        _1077_rTypeArg = _out34;
        _1063_fields = Dafny.Sequence<RAST._IField>.Concat(_1063_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1074_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1077_rTypeArg))))));
        _1064_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1064_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1074_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      Dafny.ISequence<Dafny.Rune> _1078_datatypeName;
      _1078_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IStruct _1079_struct;
      _1079_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1078_datatypeName, _1060_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1063_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1079_struct));
      Dafny.ISequence<RAST._IImplMember> _1080_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1081_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out35;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out36;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(path, (c).dtor_attributes))), _1058_typeParamsSet, out _out35, out _out36);
      _1080_implBodyRaw = _out35;
      _1081_traitBodies = _out36;
      Dafny.ISequence<RAST._IImplMember> _1082_implBody;
      _1082_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(RAST.Expr.create_Identifier(_1078_datatypeName), _1064_fieldInits))))), _1080_implBodyRaw);
      RAST._IImpl _1083_i;
      _1083_i = RAST.Impl.create_Impl(_1060_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1078_datatypeName), _1059_rTypeParams), _1061_whereConstraints, _1082_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1083_i)));
      if ((new BigInteger(((c).dtor_superClasses).Count)).Sign == 1) {
        BigInteger _1084_i;
        _1084_i = BigInteger.Zero;
        while ((_1084_i) < (new BigInteger(((c).dtor_superClasses).Count))) {
          DAST._IType _1085_superClass;
          _1085_superClass = ((c).dtor_superClasses).Select(_1084_i);
          DAST._IType _source46 = _1085_superClass;
          bool unmatched46 = true;
          if (unmatched46) {
            if (_source46.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1086_traitPath = _source46.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _1087_typeArgs = _source46.dtor_typeArgs;
              DAST._IResolvedType resolved0 = _source46.dtor_resolved;
              if (resolved0.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1088___v44 = resolved0.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1089___v45 = resolved0.dtor_attributes;
                unmatched46 = false;
                {
                  RAST._IType _1090_pathStr;
                  RAST._IType _out37;
                  _out37 = DCOMP.COMP.GenPath(_1086_traitPath);
                  _1090_pathStr = _out37;
                  Dafny.ISequence<RAST._IType> _1091_typeArgs;
                  Dafny.ISequence<RAST._IType> _out38;
                  _out38 = (this).GenTypeArgs(_1087_typeArgs, false, false);
                  _1091_typeArgs = _out38;
                  Dafny.ISequence<RAST._IImplMember> _1092_body;
                  _1092_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((_1081_traitBodies).Contains(_1086_traitPath)) {
                    _1092_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1081_traitBodies,_1086_traitPath);
                  }
                  RAST._IType _1093_genSelfPath;
                  RAST._IType _out39;
                  _out39 = DCOMP.COMP.GenPath(path);
                  _1093_genSelfPath = _out39;
                  RAST._IModDecl _1094_x;
                  _1094_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1060_rTypeParamsDecls, RAST.Type.create_TypeApp(_1090_pathStr, _1091_typeArgs), RAST.__default.Rc(RAST.Type.create_TypeApp(_1093_genSelfPath, _1059_rTypeParams)), _1061_whereConstraints, _1092_body));
                  s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1094_x));
                }
              }
            }
          }
          if (unmatched46) {
            DAST._IType _1095___v46 = _source46;
            unmatched46 = false;
          }
          _1084_i = (_1084_i) + (BigInteger.One);
        }
      }
      RAST._IImpl _1096_d;
      _1096_d = RAST.Impl.create_ImplFor(_1060_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1078_datatypeName), _1059_rTypeParams), _1061_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(_1078_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new()"))))))));
      Dafny.ISequence<RAST._IModDecl> _1097_defaultImpl;
      _1097_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1096_d));
      RAST._IImpl _1098_p;
      _1098_p = RAST.Impl.create_ImplFor(_1060_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1078_datatypeName), _1059_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), DCOMP.__default.escapeName(((c).dtor_enclosingModule))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")"))))))));
      Dafny.ISequence<RAST._IModDecl> _1099_printImpl;
      _1099_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1098_p));
      RAST._IImpl _1100_pp;
      _1100_pp = RAST.Impl.create_ImplFor(_1060_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cmp::PartialEq")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1078_datatypeName), _1059_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("eq"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.__default.SelfBorrowed)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ptr::eq(self, other)")))))));
      Dafny.ISequence<RAST._IModDecl> _1101_ptrPartialEqImpl;
      _1101_ptrPartialEqImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1100_pp));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(s, _1097_defaultImpl), _1099_printImpl), _1101_ptrPartialEqImpl);
      return s;
    }
    public Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _1102_typeParamsSet;
      _1102_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1103_typeParamDecls;
      _1103_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1104_typeParams;
      _1104_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1105_tpI;
      _1105_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        while ((_1105_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._ITypeArgDecl _1106_tp;
          _1106_tp = ((t).dtor_typeParams).Select(_1105_tpI);
          DAST._IType _1107_typeArg;
          RAST._ITypeParamDecl _1108_typeParamDecl;
          DAST._IType _out40;
          RAST._ITypeParamDecl _out41;
          (this).GenTypeParam(_1106_tp, out _out40, out _out41);
          _1107_typeArg = _out40;
          _1108_typeParamDecl = _out41;
          _1102_typeParamsSet = Dafny.Set<DAST._IType>.Union(_1102_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1107_typeArg));
          _1103_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1103_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1108_typeParamDecl));
          RAST._IType _1109_typeParam;
          RAST._IType _out42;
          _out42 = (this).GenType(_1107_typeArg, false, false);
          _1109_typeParam = _out42;
          _1104_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1104_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1109_typeParam));
          _1105_tpI = (_1105_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1110_fullPath;
      _1110_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1111_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1112___v47;
      Dafny.ISequence<RAST._IImplMember> _out43;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out44;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_1110_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_1110_fullPath, (t).dtor_attributes)), _1102_typeParamsSet, out _out43, out _out44);
      _1111_implBody = _out43;
      _1112___v47 = _out44;
      s = (RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1103_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1104_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1111_implBody)))._ToString(DCOMP.__default.IND);
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1113_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1114_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1115_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1116_whereConstraints;
      Dafny.ISet<DAST._IType> _out45;
      Dafny.ISequence<RAST._IType> _out46;
      Dafny.ISequence<RAST._ITypeParamDecl> _out47;
      Dafny.ISequence<Dafny.Rune> _out48;
      (this).GenTypeParameters((c).dtor_typeParams, out _out45, out _out46, out _out47, out _out48);
      _1113_typeParamsSet = _out45;
      _1114_rTypeParams = _out46;
      _1115_rTypeParamsDecls = _out47;
      _1116_whereConstraints = _out48;
      Dafny.ISequence<Dafny.Rune> _1117_constrainedTypeParams;
      _1117_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1115_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1118_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source47 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      bool unmatched47 = true;
      if (unmatched47) {
        if (_source47.is_Some) {
          RAST._IType _1119_v = _source47.dtor_value;
          unmatched47 = false;
          _1118_underlyingType = _1119_v;
        }
      }
      if (unmatched47) {
        unmatched47 = false;
        RAST._IType _out49;
        _out49 = (this).GenType((c).dtor_base, false, false);
        _1118_underlyingType = _out49;
      }
      DAST._IType _1120_resultingType;
      _1120_resultingType = DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Newtype((c).dtor_base, (c).dtor_range, false, (c).dtor_attributes));
      Dafny.ISequence<Dafny.Rune> _1121_datatypeName;
      _1121_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1121_datatypeName, _1115_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1118_underlyingType))))));
      RAST._IExpr _1122_fnBody;
      _1122_fnBody = RAST.Expr.create_Identifier(_1121_datatypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source48 = (c).dtor_witnessExpr;
      bool unmatched48 = true;
      if (unmatched48) {
        if (_source48.is_Some) {
          DAST._IExpression _1123_e = _source48.dtor_value;
          unmatched48 = false;
          {
            DAST._IExpression _1124_e;
            _1124_e = ((object.Equals((c).dtor_base, _1120_resultingType)) ? (_1123_e) : (DAST.Expression.create_Convert(_1123_e, (c).dtor_base, _1120_resultingType)));
            RAST._IExpr _1125_eStr;
            DCOMP._IOwnership _1126___v48;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1127___v49;
            RAST._IExpr _out50;
            DCOMP._IOwnership _out51;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out52;
            (this).GenExpr(_1124_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out50, out _out51, out _out52);
            _1125_eStr = _out50;
            _1126___v48 = _out51;
            _1127___v49 = _out52;
            _1122_fnBody = (_1122_fnBody).Apply1(_1125_eStr);
          }
        }
      }
      if (unmatched48) {
        unmatched48 = false;
        {
          _1122_fnBody = (_1122_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1128_body;
      _1128_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1122_fnBody)));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1115_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1121_datatypeName), _1114_rTypeParams), _1116_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1128_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1115_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1121_datatypeName), _1114_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1115_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1121_datatypeName), _1114_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1118_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1129_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1130_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1131_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1132_whereConstraints;
      Dafny.ISet<DAST._IType> _out53;
      Dafny.ISequence<RAST._IType> _out54;
      Dafny.ISequence<RAST._ITypeParamDecl> _out55;
      Dafny.ISequence<Dafny.Rune> _out56;
      (this).GenTypeParameters((c).dtor_typeParams, out _out53, out _out54, out _out55, out _out56);
      _1129_typeParamsSet = _out53;
      _1130_rTypeParams = _out54;
      _1131_rTypeParamsDecls = _out55;
      _1132_whereConstraints = _out56;
      Dafny.ISequence<Dafny.Rune> _1133_datatypeName;
      _1133_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1134_ctors;
      _1134_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      BigInteger _hi9 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1135_i = BigInteger.Zero; _1135_i < _hi9; _1135_i++) {
        DAST._IDatatypeCtor _1136_ctor;
        _1136_ctor = ((c).dtor_ctors).Select(_1135_i);
        Dafny.ISequence<RAST._IField> _1137_ctorArgs;
        _1137_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1138_isNumeric;
        _1138_isNumeric = false;
        BigInteger _hi10 = new BigInteger(((_1136_ctor).dtor_args).Count);
        for (BigInteger _1139_j = BigInteger.Zero; _1139_j < _hi10; _1139_j++) {
          DAST._IDatatypeDtor _1140_dtor;
          _1140_dtor = ((_1136_ctor).dtor_args).Select(_1139_j);
          RAST._IType _1141_formalType;
          RAST._IType _out57;
          _out57 = (this).GenType(((_1140_dtor).dtor_formal).dtor_typ, false, false);
          _1141_formalType = _out57;
          Dafny.ISequence<Dafny.Rune> _1142_formalName;
          _1142_formalName = DCOMP.__default.escapeName(((_1140_dtor).dtor_formal).dtor_name);
          if (((_1139_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1142_formalName))) {
            _1138_isNumeric = true;
          }
          if ((((_1139_j).Sign != 0) && (_1138_isNumeric)) && (!(Std.Strings.__default.OfNat(_1139_j)).Equals(_1142_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1142_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1139_j)));
            _1138_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1137_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1137_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1142_formalName, RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1141_formalType))))));
          } else {
            _1137_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1137_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1142_formalName, _1141_formalType))));
          }
        }
        RAST._IFields _1143_namedFields;
        _1143_namedFields = RAST.Fields.create_NamedFields(_1137_ctorArgs);
        if (_1138_isNumeric) {
          _1143_namedFields = (_1143_namedFields).ToNamelessFields();
        }
        _1134_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1134_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1136_ctor).dtor_name), _1143_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1144_selfPath;
      _1144_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1145_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1146_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out58;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out59;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(_1144_selfPath, (c).dtor_attributes))), _1129_typeParamsSet, out _out58, out _out59);
      _1145_implBodyRaw = _out58;
      _1146_traitBodies = _out59;
      Dafny.ISequence<RAST._IImplMember> _1147_implBody;
      _1147_implBody = _1145_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1148_emittedFields;
      _1148_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi11 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1149_i = BigInteger.Zero; _1149_i < _hi11; _1149_i++) {
        DAST._IDatatypeCtor _1150_ctor;
        _1150_ctor = ((c).dtor_ctors).Select(_1149_i);
        BigInteger _hi12 = new BigInteger(((_1150_ctor).dtor_args).Count);
        for (BigInteger _1151_j = BigInteger.Zero; _1151_j < _hi12; _1151_j++) {
          DAST._IDatatypeDtor _1152_dtor;
          _1152_dtor = ((_1150_ctor).dtor_args).Select(_1151_j);
          Dafny.ISequence<Dafny.Rune> _1153_callName;
          _1153_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1152_dtor).dtor_callName, DCOMP.__default.escapeName(((_1152_dtor).dtor_formal).dtor_name));
          if (!((_1148_emittedFields).Contains(_1153_callName))) {
            _1148_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1148_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1153_callName));
            RAST._IType _1154_formalType;
            RAST._IType _out60;
            _out60 = (this).GenType(((_1152_dtor).dtor_formal).dtor_typ, false, false);
            _1154_formalType = _out60;
            Dafny.ISequence<RAST._IMatchCase> _1155_cases;
            _1155_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1156_k = BigInteger.Zero; _1156_k < _hi13; _1156_k++) {
              DAST._IDatatypeCtor _1157_ctor2;
              _1157_ctor2 = ((c).dtor_ctors).Select(_1156_k);
              Dafny.ISequence<Dafny.Rune> _1158_pattern;
              _1158_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1133_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1157_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1159_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1160_hasMatchingField;
              _1160_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1161_patternInner;
              _1161_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1162_isNumeric;
              _1162_isNumeric = false;
              BigInteger _hi14 = new BigInteger(((_1157_ctor2).dtor_args).Count);
              for (BigInteger _1163_l = BigInteger.Zero; _1163_l < _hi14; _1163_l++) {
                DAST._IDatatypeDtor _1164_dtor2;
                _1164_dtor2 = ((_1157_ctor2).dtor_args).Select(_1163_l);
                Dafny.ISequence<Dafny.Rune> _1165_patternName;
                _1165_patternName = DCOMP.__default.escapeName(((_1164_dtor2).dtor_formal).dtor_name);
                if (((_1163_l).Sign == 0) && ((_1165_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1162_isNumeric = true;
                }
                if (_1162_isNumeric) {
                  _1165_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1164_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1163_l)));
                }
                if (object.Equals(((_1152_dtor).dtor_formal).dtor_name, ((_1164_dtor2).dtor_formal).dtor_name)) {
                  _1160_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1165_patternName);
                }
                _1161_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1161_patternInner, _1165_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1162_isNumeric) {
                _1158_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1158_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1161_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1158_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1158_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1161_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1160_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1159_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1160_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1159_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1160_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1159_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _1166_ctorMatch;
              _1166_ctorMatch = RAST.MatchCase.create(_1158_pattern, RAST.Expr.create_RawExpr(_1159_rhs));
              _1155_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1155_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1166_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1155_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1155_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1133_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _1167_methodBody;
            _1167_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1155_cases);
            _1147_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1147_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1153_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1154_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1167_methodBody)))));
          }
        }
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1168_types;
        _1168_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi15 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1169_typeI = BigInteger.Zero; _1169_typeI < _hi15; _1169_typeI++) {
          DAST._IType _1170_typeArg;
          RAST._ITypeParamDecl _1171_rTypeParamDecl;
          DAST._IType _out61;
          RAST._ITypeParamDecl _out62;
          (this).GenTypeParam(((c).dtor_typeParams).Select(_1169_typeI), out _out61, out _out62);
          _1170_typeArg = _out61;
          _1171_rTypeParamDecl = _out62;
          RAST._IType _1172_rTypeArg;
          RAST._IType _out63;
          _out63 = (this).GenType(_1170_typeArg, false, false);
          _1172_rTypeArg = _out63;
          _1168_types = Dafny.Sequence<RAST._IType>.Concat(_1168_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1172_rTypeArg))));
        }
        _1134_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1134_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1173_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1173_tpe);
})), _1168_types)))));
      }
      Dafny.ISequence<RAST._IModDecl> _1174_enumBody;
      _1174_enumBody = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]")), _1133_datatypeName, _1131_rTypeParamsDecls, _1134_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1131_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1133_datatypeName), _1130_rTypeParams), _1132_whereConstraints, _1147_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1175_printImplBodyCases;
      _1175_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1176_i = BigInteger.Zero; _1176_i < _hi16; _1176_i++) {
        DAST._IDatatypeCtor _1177_ctor;
        _1177_ctor = ((c).dtor_ctors).Select(_1176_i);
        Dafny.ISequence<Dafny.Rune> _1178_ctorMatch;
        _1178_ctorMatch = DCOMP.__default.escapeName((_1177_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1179_modulePrefix;
        _1179_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1180_ctorName;
        _1180_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1179_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1177_ctor).dtor_name));
        if (((new BigInteger((_1180_ctorName).Count)) >= (new BigInteger(13))) && (((_1180_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1180_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1181_printRhs;
        _1181_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1180_ctorName), (((_1177_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        bool _1182_isNumeric;
        _1182_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1183_ctorMatchInner;
        _1183_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi17 = new BigInteger(((_1177_ctor).dtor_args).Count);
        for (BigInteger _1184_j = BigInteger.Zero; _1184_j < _hi17; _1184_j++) {
          DAST._IDatatypeDtor _1185_dtor;
          _1185_dtor = ((_1177_ctor).dtor_args).Select(_1184_j);
          Dafny.ISequence<Dafny.Rune> _1186_patternName;
          _1186_patternName = DCOMP.__default.escapeName(((_1185_dtor).dtor_formal).dtor_name);
          if (((_1184_j).Sign == 0) && ((_1186_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1182_isNumeric = true;
          }
          if (_1182_isNumeric) {
            _1186_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1185_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1184_j)));
          }
          _1183_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1183_ctorMatchInner, _1186_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1184_j).Sign == 1) {
            _1181_printRhs = (_1181_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1181_printRhs = (_1181_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1186_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))));
        }
        if (_1182_isNumeric) {
          _1178_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1178_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1183_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1178_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1178_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1183_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1177_ctor).dtor_hasAnyArgs) {
          _1181_printRhs = (_1181_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1181_printRhs = (_1181_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1175_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1175_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1133_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1178_ctorMatch), RAST.Expr.create_Block(_1181_printRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _1175_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1175_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1133_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1187_defaultConstrainedTypeParams;
      _1187_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1131_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      RAST._IExpr _1188_printImplBody;
      _1188_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1175_printImplBodyCases);
      Dafny.ISequence<RAST._IModDecl> _1189_printImpl;
      _1189_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1131_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1133_datatypeName), _1130_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1131_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1133_datatypeName), _1130_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1188_printImplBody)))))));
      Dafny.ISequence<RAST._IModDecl> _1190_defaultImpl;
      _1190_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      Dafny.ISequence<RAST._IModDecl> _1191_asRefImpl;
      _1191_asRefImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1192_structName;
        _1192_structName = (RAST.Expr.create_Identifier(_1133_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1193_structAssignments;
        _1193_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi18 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1194_i = BigInteger.Zero; _1194_i < _hi18; _1194_i++) {
          DAST._IDatatypeDtor _1195_dtor;
          _1195_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1194_i);
          _1193_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1193_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1195_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1196_defaultConstrainedTypeParams;
        _1196_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1131_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1197_fullType;
        _1197_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1133_datatypeName), _1130_rTypeParams);
        _1190_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1196_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1197_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1197_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1192_structName, _1193_structAssignments))))))));
        _1191_asRefImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1131_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_1197_fullType), RAST.Type.create_Borrowed(_1197_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self)))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(_1174_enumBody, _1189_printImpl), _1190_defaultImpl), _1191_asRefImpl);
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
        for (BigInteger _1198_i = BigInteger.Zero; _1198_i < _hi19; _1198_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1198_i))));
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
        for (BigInteger _1199_i = BigInteger.Zero; _1199_i < _hi20; _1199_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1199_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding, bool inFn)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger((args).Count)).Sign == 1) {
        BigInteger _1200_i;
        _1200_i = BigInteger.Zero;
        while ((_1200_i) < (new BigInteger((args).Count))) {
          RAST._IType _1201_genTp;
          RAST._IType _out64;
          _out64 = (this).GenType((args).Select(_1200_i), inBinding, inFn);
          _1201_genTp = _out64;
          s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1201_genTp));
          _1200_i = (_1200_i) + (BigInteger.One);
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
      DAST._IType _source49 = c;
      bool unmatched49 = true;
      if (unmatched49) {
        if (_source49.is_Path) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1202_p = _source49.dtor_Path_a0;
          Dafny.ISequence<DAST._IType> _1203_args = _source49.dtor_typeArgs;
          DAST._IResolvedType _1204_resolved = _source49.dtor_resolved;
          unmatched49 = false;
          {
            RAST._IType _1205_t;
            RAST._IType _out65;
            _out65 = DCOMP.COMP.GenPath(_1202_p);
            _1205_t = _out65;
            Dafny.ISequence<RAST._IType> _1206_typeArgs;
            Dafny.ISequence<RAST._IType> _out66;
            _out66 = (this).GenTypeArgs(_1203_args, inBinding, inFn);
            _1206_typeArgs = _out66;
            s = RAST.Type.create_TypeApp(_1205_t, _1206_typeArgs);
            DAST._IResolvedType _source50 = _1204_resolved;
            bool unmatched50 = true;
            if (unmatched50) {
              if (_source50.is_Datatype) {
                DAST._IDatatypeType datatypeType0 = _source50.dtor_datatypeType;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1207___v50 = datatypeType0.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1208_attributes = datatypeType0.dtor_attributes;
                unmatched50 = false;
                {
                  if ((this).IsRcWrapped(_1208_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched50) {
              if (_source50.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1209___v51 = _source50.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1210___v52 = _source50.dtor_attributes;
                unmatched50 = false;
                {
                  if ((_1202_p).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
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
            if (unmatched50) {
              DAST._IType _1211_t = _source50.dtor_baseType;
              DAST._INewtypeRange _1212_range = _source50.dtor_range;
              bool _1213_erased = _source50.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1214_attributes = _source50.dtor_attributes;
              unmatched50 = false;
              {
                if (_1213_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source51 = DCOMP.COMP.NewtypeToRustType(_1211_t, _1212_range);
                  bool unmatched51 = true;
                  if (unmatched51) {
                    if (_source51.is_Some) {
                      RAST._IType _1215_v = _source51.dtor_value;
                      unmatched51 = false;
                      s = _1215_v;
                    }
                  }
                  if (unmatched51) {
                    unmatched51 = false;
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Nullable) {
          DAST._IType _1216_inner = _source49.dtor_Nullable_a0;
          unmatched49 = false;
          {
            RAST._IType _1217_innerExpr;
            RAST._IType _out67;
            _out67 = (this).GenType(_1216_inner, inBinding, inFn);
            _1217_innerExpr = _out67;
            s = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::option::Option")), Dafny.Sequence<RAST._IType>.FromElements(_1217_innerExpr));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1218_types = _source49.dtor_Tuple_a0;
          unmatched49 = false;
          {
            Dafny.ISequence<RAST._IType> _1219_args;
            _1219_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1220_i;
            _1220_i = BigInteger.Zero;
            while ((_1220_i) < (new BigInteger((_1218_types).Count))) {
              RAST._IType _1221_generated;
              RAST._IType _out68;
              _out68 = (this).GenType((_1218_types).Select(_1220_i), inBinding, inFn);
              _1221_generated = _out68;
              _1219_args = Dafny.Sequence<RAST._IType>.Concat(_1219_args, Dafny.Sequence<RAST._IType>.FromElements(_1221_generated));
              _1220_i = (_1220_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1218_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1219_args)) : (RAST.__default.SystemTupleType(_1219_args)));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Array) {
          DAST._IType _1222_element = _source49.dtor_element;
          BigInteger _1223_dims = _source49.dtor_dims;
          unmatched49 = false;
          {
            RAST._IType _1224_elem;
            RAST._IType _out69;
            _out69 = (this).GenType(_1222_element, inBinding, inFn);
            _1224_elem = _out69;
            s = _1224_elem;
            BigInteger _1225_i;
            _1225_i = BigInteger.Zero;
            while ((_1225_i) < (_1223_dims)) {
              s = RAST.__default.Rc(RAST.__default.RefCell(RAST.__default.Vec(s)));
              _1225_i = (_1225_i) + (BigInteger.One);
            }
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Seq) {
          DAST._IType _1226_element = _source49.dtor_element;
          unmatched49 = false;
          {
            RAST._IType _1227_elem;
            RAST._IType _out70;
            _out70 = (this).GenType(_1226_element, inBinding, inFn);
            _1227_elem = _out70;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1227_elem));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Set) {
          DAST._IType _1228_element = _source49.dtor_element;
          unmatched49 = false;
          {
            RAST._IType _1229_elem;
            RAST._IType _out71;
            _out71 = (this).GenType(_1228_element, inBinding, inFn);
            _1229_elem = _out71;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1229_elem));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Multiset) {
          DAST._IType _1230_element = _source49.dtor_element;
          unmatched49 = false;
          {
            RAST._IType _1231_elem;
            RAST._IType _out72;
            _out72 = (this).GenType(_1230_element, inBinding, inFn);
            _1231_elem = _out72;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1231_elem));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Map) {
          DAST._IType _1232_key = _source49.dtor_key;
          DAST._IType _1233_value = _source49.dtor_value;
          unmatched49 = false;
          {
            RAST._IType _1234_keyType;
            RAST._IType _out73;
            _out73 = (this).GenType(_1232_key, inBinding, inFn);
            _1234_keyType = _out73;
            RAST._IType _1235_valueType;
            RAST._IType _out74;
            _out74 = (this).GenType(_1233_value, inBinding, inFn);
            _1235_valueType = _out74;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1234_keyType, _1235_valueType));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_MapBuilder) {
          DAST._IType _1236_key = _source49.dtor_key;
          DAST._IType _1237_value = _source49.dtor_value;
          unmatched49 = false;
          {
            RAST._IType _1238_keyType;
            RAST._IType _out75;
            _out75 = (this).GenType(_1236_key, inBinding, inFn);
            _1238_keyType = _out75;
            RAST._IType _1239_valueType;
            RAST._IType _out76;
            _out76 = (this).GenType(_1237_value, inBinding, inFn);
            _1239_valueType = _out76;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1238_keyType, _1239_valueType));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_SetBuilder) {
          DAST._IType _1240_elem = _source49.dtor_element;
          unmatched49 = false;
          {
            RAST._IType _1241_elemType;
            RAST._IType _out77;
            _out77 = (this).GenType(_1240_elem, inBinding, inFn);
            _1241_elemType = _out77;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1241_elemType));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1242_args = _source49.dtor_args;
          DAST._IType _1243_result = _source49.dtor_result;
          unmatched49 = false;
          {
            Dafny.ISequence<RAST._IType> _1244_argTypes;
            _1244_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1245_i;
            _1245_i = BigInteger.Zero;
            while ((_1245_i) < (new BigInteger((_1242_args).Count))) {
              RAST._IType _1246_generated;
              RAST._IType _out78;
              _out78 = (this).GenType((_1242_args).Select(_1245_i), inBinding, true);
              _1246_generated = _out78;
              _1244_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1244_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1246_generated)));
              _1245_i = (_1245_i) + (BigInteger.One);
            }
            RAST._IType _1247_resultType;
            RAST._IType _out79;
            _out79 = (this).GenType(_1243_result, inBinding, (inFn) || (inBinding));
            _1247_resultType = _out79;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1244_argTypes, _1247_resultType)));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h100 = _source49.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1248_name = _h100;
          unmatched49 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1248_name));
        }
      }
      if (unmatched49) {
        if (_source49.is_Primitive) {
          DAST._IPrimitive _1249_p = _source49.dtor_Primitive_a0;
          unmatched49 = false;
          {
            DAST._IPrimitive _source52 = _1249_p;
            bool unmatched52 = true;
            if (unmatched52) {
              if (_source52.is_Int) {
                unmatched52 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
              }
            }
            if (unmatched52) {
              if (_source52.is_Real) {
                unmatched52 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
              }
            }
            if (unmatched52) {
              if (_source52.is_String) {
                unmatched52 = false;
                s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
              }
            }
            if (unmatched52) {
              if (_source52.is_Bool) {
                unmatched52 = false;
                s = RAST.Type.create_Bool();
              }
            }
            if (unmatched52) {
              unmatched52 = false;
              s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
            }
          }
        }
      }
      if (unmatched49) {
        Dafny.ISequence<Dafny.Rune> _1250_v = _source49.dtor_Passthrough_a0;
        unmatched49 = false;
        s = RAST.__default.RawType(_1250_v);
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
      for (BigInteger _1251_i = BigInteger.Zero; _1251_i < _hi21; _1251_i++) {
        DAST._IMethod _source53 = (body).Select(_1251_i);
        bool unmatched53 = true;
        if (unmatched53) {
          DAST._IMethod _1252_m = _source53;
          unmatched53 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source54 = (_1252_m).dtor_overridingPath;
            bool unmatched54 = true;
            if (unmatched54) {
              if (_source54.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1253_p = _source54.dtor_value;
                unmatched54 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1254_existing;
                  _1254_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1253_p)) {
                    _1254_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1253_p);
                  }
                  RAST._IImplMember _1255_genMethod;
                  RAST._IImplMember _out80;
                  _out80 = (this).GenMethod(_1252_m, true, enclosingType, enclosingTypeParams);
                  _1255_genMethod = _out80;
                  _1254_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1254_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1255_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1253_p, _1254_existing)));
                }
              }
            }
            if (unmatched54) {
              unmatched54 = false;
              {
                RAST._IImplMember _1256_generated;
                RAST._IImplMember _out81;
                _out81 = (this).GenMethod(_1252_m, forTrait, enclosingType, enclosingTypeParams);
                _1256_generated = _out81;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1256_generated));
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
      for (BigInteger _1257_i = BigInteger.Zero; _1257_i < _hi22; _1257_i++) {
        DAST._IFormal _1258_param;
        _1258_param = (@params).Select(_1257_i);
        RAST._IType _1259_paramType;
        RAST._IType _out82;
        _out82 = (this).GenType((_1258_param).dtor_typ, false, false);
        _1259_paramType = _out82;
        if ((!((_1259_paramType).CanReadWithoutClone())) && (!((_1258_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1259_paramType = RAST.Type.create_Borrowed(_1259_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_1258_param).dtor_name), _1259_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1260_params;
      Dafny.ISequence<RAST._IFormal> _out83;
      _out83 = (this).GenParams((m).dtor_params);
      _1260_params = _out83;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1261_paramNames;
      _1261_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1262_paramTypes;
      _1262_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi23 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1263_paramI = BigInteger.Zero; _1263_paramI < _hi23; _1263_paramI++) {
        DAST._IFormal _1264_dafny__formal;
        _1264_dafny__formal = ((m).dtor_params).Select(_1263_paramI);
        RAST._IFormal _1265_formal;
        _1265_formal = (_1260_params).Select(_1263_paramI);
        Dafny.ISequence<Dafny.Rune> _1266_name;
        _1266_name = (_1265_formal).dtor_name;
        _1261_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1261_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1266_name));
        _1262_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1262_paramTypes, _1266_name, (_1265_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1267_fnName;
      _1267_fnName = DCOMP.__default.escapeName((m).dtor_name);
      Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1268_selfIdentifier;
      _1268_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1269_selfId;
        _1269_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((_1267_fnName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_ctor"))) {
          _1269_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        if (forTrait) {
          RAST._IFormal _1270_selfFormal;
          _1270_selfFormal = RAST.Formal.selfBorrowedMut;
          _1260_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1270_selfFormal), _1260_params);
        } else {
          RAST._IType _1271_tpe;
          RAST._IType _out84;
          _out84 = (this).GenType(enclosingType, false, false);
          _1271_tpe = _out84;
          if (!((_1271_tpe).CanReadWithoutClone())) {
            _1271_tpe = RAST.Type.create_Borrowed(_1271_tpe);
          }
          _1260_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1269_selfId, _1271_tpe)), _1260_params);
        }
        _1268_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1269_selfId);
      }
      Dafny.ISequence<RAST._IType> _1272_retTypeArgs;
      _1272_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1273_typeI;
      _1273_typeI = BigInteger.Zero;
      while ((_1273_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1274_typeExpr;
        RAST._IType _out85;
        _out85 = (this).GenType(((m).dtor_outTypes).Select(_1273_typeI), false, false);
        _1274_typeExpr = _out85;
        _1272_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1272_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1274_typeExpr));
        _1273_typeI = (_1273_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1275_visibility;
      _1275_visibility = RAST.Visibility.create_PUB();
      Dafny.ISequence<DAST._ITypeArgDecl> _1276_typeParamsFiltered;
      _1276_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi24 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1277_typeParamI = BigInteger.Zero; _1277_typeParamI < _hi24; _1277_typeParamI++) {
        DAST._ITypeArgDecl _1278_typeParam;
        _1278_typeParam = ((m).dtor_typeParams).Select(_1277_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1278_typeParam).dtor_name)))) {
          _1276_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1276_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1278_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1279_typeParams;
      _1279_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1276_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi25 = new BigInteger((_1276_typeParamsFiltered).Count);
        for (BigInteger _1280_i = BigInteger.Zero; _1280_i < _hi25; _1280_i++) {
          DAST._IType _1281_typeArg;
          RAST._ITypeParamDecl _1282_rTypeParamDecl;
          DAST._IType _out86;
          RAST._ITypeParamDecl _out87;
          (this).GenTypeParam((_1276_typeParamsFiltered).Select(_1280_i), out _out86, out _out87);
          _1281_typeArg = _out86;
          _1282_rTypeParamDecl = _out87;
          var _pat_let_tv101 = _1282_rTypeParamDecl;
          _1282_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1282_rTypeParamDecl, _pat_let6_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let6_0, _1283_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Dafny.Sequence<RAST._IType>.Concat((_pat_let_tv101).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default")))), _pat_let7_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let7_0, _1284_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1283_dt__update__tmp_h0).dtor_content, _1284_dt__update_hconstraints_h0)))));
          _1279_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1279_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1282_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1285_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1286_env = DCOMP.Environment.Default();
      RAST._IExpr _1287_preBody;
      _1287_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      if ((m).dtor_hasBody) {
        RAST._IExpr _1288_earlyReturn;
        _1288_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source55 = (m).dtor_outVars;
        bool unmatched55 = true;
        if (unmatched55) {
          if (_source55.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1289_outVars = _source55.dtor_value;
            unmatched55 = false;
            {
              Dafny.ISequence<RAST._IExpr> _1290_tupleArgs;
              _1290_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi26 = new BigInteger((_1289_outVars).Count);
              for (BigInteger _1291_outI = BigInteger.Zero; _1291_outI < _hi26; _1291_outI++) {
                Dafny.ISequence<Dafny.Rune> _1292_outVar;
                _1292_outVar = (_1289_outVars).Select(_1291_outI);
                RAST._IType _1293_outType;
                RAST._IType _out88;
                _out88 = (this).GenType(((m).dtor_outTypes).Select(_1291_outI), false, false);
                _1293_outType = _out88;
                Dafny.ISequence<Dafny.Rune> _1294_outName;
                _1294_outName = DCOMP.__default.escapeName((_1292_outVar));
                _1261_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1261_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1294_outName));
                RAST._IType _1295_outMaybeType;
                _1295_outMaybeType = (((_1293_outType).CanReadWithoutClone()) ? (_1293_outType) : (RAST.Type.create_Borrowed(_1293_outType)));
                _1262_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1262_paramTypes, _1294_outName, _1295_outMaybeType);
                RAST._IExpr _1296_outVarReturn;
                DCOMP._IOwnership _1297___v53;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1298___v54;
                RAST._IExpr _out89;
                DCOMP._IOwnership _out90;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out91;
                (this).GenExpr(DAST.Expression.create_Ident((_1292_outVar)), Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1294_outName), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>, RAST._IType>(_1294_outName, _1295_outMaybeType))), DCOMP.Ownership.create_OwnershipOwned(), out _out89, out _out90, out _out91);
                _1296_outVarReturn = _out89;
                _1297___v53 = _out90;
                _1298___v54 = _out91;
                _1290_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1290_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1296_outVarReturn));
              }
              if ((new BigInteger((_1290_tupleArgs).Count)) == (BigInteger.One)) {
                _1288_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1290_tupleArgs).Select(BigInteger.Zero)));
              } else {
                _1288_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1290_tupleArgs)));
              }
            }
          }
        }
        if (unmatched55) {
          unmatched55 = false;
        }
        _1286_env = DCOMP.Environment.create(_1261_paramNames, _1262_paramTypes);
        RAST._IExpr _1299_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1300___v55;
        DCOMP._IEnvironment _1301___v56;
        RAST._IExpr _out92;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out93;
        DCOMP._IEnvironment _out94;
        (this).GenStmts((m).dtor_body, _1268_selfIdentifier, _1286_env, true, _1288_earlyReturn, out _out92, out _out93, out _out94);
        _1299_body = _out92;
        _1300___v55 = _out93;
        _1301___v56 = _out94;
        _1285_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1287_preBody).Then(_1299_body));
      } else {
        _1286_env = DCOMP.Environment.create(_1261_paramNames, _1262_paramTypes);
        _1285_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1275_visibility, RAST.Fn.create(_1267_fnName, _1279_typeParams, _1260_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1272_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1272_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1272_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1285_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1302_declarations;
      _1302_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1303_i;
      _1303_i = BigInteger.Zero;
      newEnv = env;
      while ((_1303_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _1304_stmt;
        _1304_stmt = (stmts).Select(_1303_i);
        RAST._IExpr _1305_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1306_recIdents;
        DCOMP._IEnvironment _1307_newEnv2;
        RAST._IExpr _out95;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out96;
        DCOMP._IEnvironment _out97;
        (this).GenStmt(_1304_stmt, selfIdent, newEnv, (isLast) && ((_1303_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out95, out _out96, out _out97);
        _1305_stmtExpr = _out95;
        _1306_recIdents = _out96;
        _1307_newEnv2 = _out97;
        newEnv = _1307_newEnv2;
        DAST._IStatement _source56 = _1304_stmt;
        bool unmatched56 = true;
        if (unmatched56) {
          if (_source56.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1308_name = _source56.dtor_name;
            DAST._IType _1309___v57 = _source56.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> _1310___v58 = _source56.dtor_maybeValue;
            unmatched56 = false;
            {
              _1302_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1302_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_1308_name)));
            }
          }
        }
        if (unmatched56) {
          DAST._IStatement _1311___v59 = _source56;
          unmatched56 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1306_recIdents, _1302_declarations));
        generated = (generated).Then(_1305_stmtExpr);
        _1303_i = (_1303_i) + (BigInteger.One);
      }
    }
    public void GenAssignLhs(DAST._IAssignLhs lhs, RAST._IExpr rhs, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, out RAST._IExpr generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      newEnv = env;
      DAST._IAssignLhs _source57 = lhs;
      bool unmatched57 = true;
      if (unmatched57) {
        if (_source57.is_Ident) {
          Dafny.ISequence<Dafny.Rune> ident0 = _source57.dtor_ident;
          Dafny.ISequence<Dafny.Rune> _1312_id = ident0;
          unmatched57 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1313_idRust;
            _1313_idRust = DCOMP.__default.escapeName(_1312_id);
            if (((env).IsBorrowed(_1313_idRust)) || ((env).IsBorrowedMut(_1313_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1313_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1313_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1313_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched57) {
        if (_source57.is_Select) {
          DAST._IExpression _1314_on = _source57.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1315_field = _source57.dtor_field;
          unmatched57 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1316_fieldName;
            _1316_fieldName = DCOMP.__default.escapeName(_1315_field);
            RAST._IExpr _1317_onExpr;
            DCOMP._IOwnership _1318_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1319_recIdents;
            RAST._IExpr _out98;
            DCOMP._IOwnership _out99;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out100;
            (this).GenExpr(_1314_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out98, out _out99, out _out100);
            _1317_onExpr = _out98;
            _1318_onOwned = _out99;
            _1319_recIdents = _out100;
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*("), (_1317_onExpr)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _1316_fieldName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()) = ")), (rhs)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";")));
            readIdents = _1319_recIdents;
            needsIIFE = true;
          }
        }
      }
      if (unmatched57) {
        DAST._IExpression _1320_on = _source57.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1321_indices = _source57.dtor_indices;
        unmatched57 = false;
        {
          RAST._IExpr _1322_onExpr;
          DCOMP._IOwnership _1323_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1324_recIdents;
          RAST._IExpr _out101;
          DCOMP._IOwnership _out102;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out103;
          (this).GenExpr(_1320_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out101, out _out102, out _out103);
          _1322_onExpr = _out101;
          _1323_onOwned = _out102;
          _1324_recIdents = _out103;
          readIdents = _1324_recIdents;
          Dafny.ISequence<Dafny.Rune> _1325_r;
          _1325_r = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          BigInteger _1326_i;
          _1326_i = BigInteger.Zero;
          while ((_1326_i) < (new BigInteger((_1321_indices).Count))) {
            RAST._IExpr _1327_idx;
            DCOMP._IOwnership _1328___v60;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1329_recIdentsIdx;
            RAST._IExpr _out104;
            DCOMP._IOwnership _out105;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out106;
            (this).GenExpr((_1321_indices).Select(_1326_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out104, out _out105, out _out106);
            _1327_idx = _out104;
            _1328___v60 = _out105;
            _1329_recIdentsIdx = _out106;
            _1325_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1325_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let __idx")), Std.Strings.__default.OfNat(_1326_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = <usize as ::dafny_runtime::NumCast>::from(")), (_1327_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap();\n"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1329_recIdentsIdx);
            _1326_i = (_1326_i) + (BigInteger.One);
          }
          _1325_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1325_r, (_1322_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()"));
          _1326_i = BigInteger.Zero;
          while ((_1326_i) < (new BigInteger((_1321_indices).Count))) {
            _1325_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1325_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[__idx")), Std.Strings.__default.OfNat(_1326_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
            _1326_i = (_1326_i) + (BigInteger.One);
          }
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1325_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), (rhs)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n}")));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source58 = stmt;
      bool unmatched58 = true;
      if (unmatched58) {
        if (_source58.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1330_name = _source58.dtor_name;
          DAST._IType _1331_typ = _source58.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source58.dtor_maybeValue;
          if (maybeValue0.is_Some) {
            DAST._IExpression _1332_expression = maybeValue0.dtor_value;
            unmatched58 = false;
            {
              RAST._IType _1333_tpe;
              RAST._IType _out107;
              _out107 = (this).GenType(_1331_typ, true, false);
              _1333_tpe = _out107;
              RAST._IExpr _1334_expr;
              DCOMP._IOwnership _1335_exprOwnership;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1336_recIdents;
              RAST._IExpr _out108;
              DCOMP._IOwnership _out109;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out110;
              (this).GenExpr(_1332_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out108, out _out109, out _out110);
              _1334_expr = _out108;
              _1335_exprOwnership = _out109;
              _1336_recIdents = _out110;
              readIdents = _1336_recIdents;
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_1330_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1333_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1334_expr));
              newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_1330_name), _1333_tpe);
            }
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1337_name = _source58.dtor_name;
          DAST._IType _1338_typ = _source58.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source58.dtor_maybeValue;
          if (maybeValue1.is_None) {
            unmatched58 = false;
            {
              DAST._IStatement _1339_newStmt;
              _1339_newStmt = DAST.Statement.create_DeclareVar(_1337_name, _1338_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1338_typ)));
              RAST._IExpr _out111;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out112;
              DCOMP._IEnvironment _out113;
              (this).GenStmt(_1339_newStmt, selfIdent, env, isLast, earlyReturn, out _out111, out _out112, out _out113);
              generated = _out111;
              readIdents = _out112;
              newEnv = _out113;
            }
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Assign) {
          DAST._IAssignLhs _1340_lhs = _source58.dtor_lhs;
          DAST._IExpression _1341_expression = _source58.dtor_value;
          unmatched58 = false;
          {
            RAST._IExpr _1342_exprGen;
            DCOMP._IOwnership _1343___v61;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1344_exprIdents;
            RAST._IExpr _out114;
            DCOMP._IOwnership _out115;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
            (this).GenExpr(_1341_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out114, out _out115, out _out116);
            _1342_exprGen = _out114;
            _1343___v61 = _out115;
            _1344_exprIdents = _out116;
            if ((_1340_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1345_rustId;
              _1345_rustId = DCOMP.__default.escapeName(((_1340_lhs).dtor_ident));
              Std.Wrappers._IOption<RAST._IType> _1346_tpe;
              _1346_tpe = (env).GetType(_1345_rustId);
            }
            RAST._IExpr _1347_lhsGen;
            bool _1348_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1349_recIdents;
            DCOMP._IEnvironment _1350_resEnv;
            RAST._IExpr _out117;
            bool _out118;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out119;
            DCOMP._IEnvironment _out120;
            (this).GenAssignLhs(_1340_lhs, _1342_exprGen, selfIdent, env, out _out117, out _out118, out _out119, out _out120);
            _1347_lhsGen = _out117;
            _1348_needsIIFE = _out118;
            _1349_recIdents = _out119;
            _1350_resEnv = _out120;
            generated = _1347_lhsGen;
            newEnv = _1350_resEnv;
            if (_1348_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1349_recIdents, _1344_exprIdents);
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_If) {
          DAST._IExpression _1351_cond = _source58.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1352_thnDafny = _source58.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1353_elsDafny = _source58.dtor_els;
          unmatched58 = false;
          {
            RAST._IExpr _1354_cond;
            DCOMP._IOwnership _1355___v62;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1356_recIdents;
            RAST._IExpr _out121;
            DCOMP._IOwnership _out122;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out123;
            (this).GenExpr(_1351_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out121, out _out122, out _out123);
            _1354_cond = _out121;
            _1355___v62 = _out122;
            _1356_recIdents = _out123;
            Dafny.ISequence<Dafny.Rune> _1357_condString;
            _1357_condString = (_1354_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1356_recIdents;
            RAST._IExpr _1358_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1359_thnIdents;
            DCOMP._IEnvironment _1360_thnEnv;
            RAST._IExpr _out124;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out125;
            DCOMP._IEnvironment _out126;
            (this).GenStmts(_1352_thnDafny, selfIdent, env, isLast, earlyReturn, out _out124, out _out125, out _out126);
            _1358_thn = _out124;
            _1359_thnIdents = _out125;
            _1360_thnEnv = _out126;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1359_thnIdents);
            RAST._IExpr _1361_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1362_elsIdents;
            DCOMP._IEnvironment _1363_elsEnv;
            RAST._IExpr _out127;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out128;
            DCOMP._IEnvironment _out129;
            (this).GenStmts(_1353_elsDafny, selfIdent, env, isLast, earlyReturn, out _out127, out _out128, out _out129);
            _1361_els = _out127;
            _1362_elsIdents = _out128;
            _1363_elsEnv = _out129;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1362_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1354_cond, _1358_thn, _1361_els);
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1364_lbl = _source58.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1365_body = _source58.dtor_body;
          unmatched58 = false;
          {
            RAST._IExpr _1366_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1367_bodyIdents;
            DCOMP._IEnvironment _1368_env2;
            RAST._IExpr _out130;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
            DCOMP._IEnvironment _out132;
            (this).GenStmts(_1365_body, selfIdent, env, isLast, earlyReturn, out _out130, out _out131, out _out132);
            _1366_body = _out130;
            _1367_bodyIdents = _out131;
            _1368_env2 = _out132;
            readIdents = _1367_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1364_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1366_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_While) {
          DAST._IExpression _1369_cond = _source58.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1370_body = _source58.dtor_body;
          unmatched58 = false;
          {
            RAST._IExpr _1371_cond;
            DCOMP._IOwnership _1372___v63;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1373_recIdents;
            RAST._IExpr _out133;
            DCOMP._IOwnership _out134;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
            (this).GenExpr(_1369_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out133, out _out134, out _out135);
            _1371_cond = _out133;
            _1372___v63 = _out134;
            _1373_recIdents = _out135;
            readIdents = _1373_recIdents;
            RAST._IExpr _1374_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1375_bodyIdents;
            DCOMP._IEnvironment _1376_bodyEnv;
            RAST._IExpr _out136;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
            DCOMP._IEnvironment _out138;
            (this).GenStmts(_1370_body, selfIdent, env, false, earlyReturn, out _out136, out _out137, out _out138);
            _1374_bodyExpr = _out136;
            _1375_bodyIdents = _out137;
            _1376_bodyEnv = _out138;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1375_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1371_cond), _1374_bodyExpr);
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1377_boundName = _source58.dtor_boundName;
          DAST._IType _1378_boundType = _source58.dtor_boundType;
          DAST._IExpression _1379_over = _source58.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1380_body = _source58.dtor_body;
          unmatched58 = false;
          {
            RAST._IExpr _1381_over;
            DCOMP._IOwnership _1382___v64;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1383_recIdents;
            RAST._IExpr _out139;
            DCOMP._IOwnership _out140;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out141;
            (this).GenExpr(_1379_over, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out139, out _out140, out _out141);
            _1381_over = _out139;
            _1382___v64 = _out140;
            _1383_recIdents = _out141;
            RAST._IType _1384_boundTpe;
            RAST._IType _out142;
            _out142 = (this).GenType(_1378_boundType, false, false);
            _1384_boundTpe = _out142;
            readIdents = _1383_recIdents;
            Dafny.ISequence<Dafny.Rune> _1385_boundRName;
            _1385_boundRName = DCOMP.__default.escapeName(_1377_boundName);
            RAST._IExpr _1386_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1387_bodyIdents;
            DCOMP._IEnvironment _1388_bodyEnv;
            RAST._IExpr _out143;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
            DCOMP._IEnvironment _out145;
            (this).GenStmts(_1380_body, selfIdent, (env).AddAssigned(_1385_boundRName, _1384_boundTpe), false, earlyReturn, out _out143, out _out144, out _out145);
            _1386_bodyExpr = _out143;
            _1387_bodyIdents = _out144;
            _1388_bodyEnv = _out145;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1387_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1385_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1385_boundRName, _1381_over, _1386_bodyExpr);
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1389_toLabel = _source58.dtor_toLabel;
          unmatched58 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source59 = _1389_toLabel;
            bool unmatched59 = true;
            if (unmatched59) {
              if (_source59.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1390_lbl = _source59.dtor_value;
                unmatched59 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1390_lbl)));
                }
              }
            }
            if (unmatched59) {
              unmatched59 = false;
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1391_body = _source58.dtor_body;
          unmatched58 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
            }
            newEnv = env;
            BigInteger _hi27 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1392_paramI = BigInteger.Zero; _1392_paramI < _hi27; _1392_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1393_param;
              _1393_param = ((env).dtor_names).Select(_1392_paramI);
              RAST._IExpr _1394_paramInit;
              DCOMP._IOwnership _1395___v65;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1396___v66;
              RAST._IExpr _out146;
              DCOMP._IOwnership _out147;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out148;
              (this).GenIdent(_1393_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out146, out _out147, out _out148);
              _1394_paramInit = _out146;
              _1395___v65 = _out147;
              _1396___v66 = _out148;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1393_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1394_paramInit)));
              if (((env).dtor_types).Contains(_1393_param)) {
                RAST._IType _1397_declaredType;
                _1397_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1393_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1393_param, _1397_declaredType);
              }
            }
            RAST._IExpr _1398_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1399_bodyIdents;
            DCOMP._IEnvironment _1400_bodyEnv;
            RAST._IExpr _out149;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out150;
            DCOMP._IEnvironment _out151;
            (this).GenStmts(_1391_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), newEnv, false, earlyReturn, out _out149, out _out150, out _out151);
            _1398_bodyExpr = _out149;
            _1399_bodyIdents = _out150;
            _1400_bodyEnv = _out151;
            readIdents = _1399_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1398_bodyExpr)));
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_JumpTailCallStart) {
          unmatched58 = false;
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Call) {
          DAST._IExpression _1401_on = _source58.dtor_on;
          DAST._ICallName _1402_name = _source58.dtor_callName;
          Dafny.ISequence<DAST._IType> _1403_typeArgs = _source58.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1404_args = _source58.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1405_maybeOutVars = _source58.dtor_outs;
          unmatched58 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IExpr _1406_onExpr;
            DCOMP._IOwnership _1407___v67;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1408_enclosingIdents;
            RAST._IExpr _out152;
            DCOMP._IOwnership _out153;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out154;
            (this).GenExpr(_1401_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out152, out _out153, out _out154);
            _1406_onExpr = _out152;
            _1407___v67 = _out153;
            _1408_enclosingIdents = _out154;
            Dafny.ISequence<RAST._IType> _1409_typeArgsR;
            _1409_typeArgsR = Dafny.Sequence<RAST._IType>.FromElements();
            if ((new BigInteger((_1403_typeArgs).Count)) >= (BigInteger.One)) {
              BigInteger _1410_typeI;
              _1410_typeI = BigInteger.Zero;
              while ((_1410_typeI) < (new BigInteger((_1403_typeArgs).Count))) {
                RAST._IType _1411_tpe;
                RAST._IType _out155;
                _out155 = (this).GenType((_1403_typeArgs).Select(_1410_typeI), false, false);
                _1411_tpe = _out155;
                _1409_typeArgsR = Dafny.Sequence<RAST._IType>.Concat(_1409_typeArgsR, Dafny.Sequence<RAST._IType>.FromElements(_1411_tpe));
                _1410_typeI = (_1410_typeI) + (BigInteger.One);
              }
            }
            Dafny.ISequence<RAST._IExpr> _1412_argExprs;
            _1412_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi28 = new BigInteger((_1404_args).Count);
            for (BigInteger _1413_i = BigInteger.Zero; _1413_i < _hi28; _1413_i++) {
              DCOMP._IOwnership _1414_argOwnership;
              _1414_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              if (((_1402_name).is_CallName) && ((_1413_i) < (new BigInteger((((_1402_name).dtor_signature)).Count)))) {
                RAST._IType _1415_tpe;
                RAST._IType _out156;
                _out156 = (this).GenType(((((_1402_name).dtor_signature)).Select(_1413_i)).dtor_typ, false, false);
                _1415_tpe = _out156;
                if ((_1415_tpe).CanReadWithoutClone()) {
                  _1414_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
                }
              }
              RAST._IExpr _1416_argExpr;
              DCOMP._IOwnership _1417_ownership;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1418_argIdents;
              RAST._IExpr _out157;
              DCOMP._IOwnership _out158;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out159;
              (this).GenExpr((_1404_args).Select(_1413_i), selfIdent, env, _1414_argOwnership, out _out157, out _out158, out _out159);
              _1416_argExpr = _out157;
              _1417_ownership = _out158;
              _1418_argIdents = _out159;
              _1412_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1412_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1416_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1418_argIdents);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1408_enclosingIdents);
            Dafny.ISequence<Dafny.Rune> _1419_renderedName;
            _1419_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
              DAST._ICallName _source60 = _1402_name;
              bool unmatched60 = true;
              if (unmatched60) {
                if (_source60.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _1420_name = _source60.dtor_name;
                  Std.Wrappers._IOption<DAST._IType> _1421___v68 = _source60.dtor_onType;
                  Dafny.ISequence<DAST._IFormal> _1422___v69 = _source60.dtor_signature;
                  unmatched60 = false;
                  return DCOMP.__default.escapeName(_1420_name);
                }
              }
              if (unmatched60) {
                bool disjunctiveMatch9 = false;
                if (_source60.is_MapBuilderAdd) {
                  disjunctiveMatch9 = true;
                }
                if (_source60.is_SetBuilderAdd) {
                  disjunctiveMatch9 = true;
                }
                if (disjunctiveMatch9) {
                  unmatched60 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                }
              }
              if (unmatched60) {
                bool disjunctiveMatch10 = false;
                disjunctiveMatch10 = true;
                disjunctiveMatch10 = true;
                if (disjunctiveMatch10) {
                  unmatched60 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                }
              }
              throw new System.Exception("unexpected control point");
            }))();
            DAST._IExpression _source61 = _1401_on;
            bool unmatched61 = true;
            if (unmatched61) {
              if (_source61.is_Companion) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1423___v70 = _source61.dtor_Companion_a0;
                unmatched61 = false;
                {
                  _1406_onExpr = (_1406_onExpr).MSel(_1419_renderedName);
                }
              }
            }
            if (unmatched61) {
              DAST._IExpression _1424___v71 = _source61;
              unmatched61 = false;
              {
                _1406_onExpr = (_1406_onExpr).Sel(_1419_renderedName);
              }
            }
            generated = _1406_onExpr;
            if ((new BigInteger((_1409_typeArgsR).Count)).Sign == 1) {
              generated = (generated).ApplyType(_1409_typeArgsR);
            }
            generated = (generated).Apply(_1412_argExprs);
            if (((_1405_maybeOutVars).is_Some) && ((new BigInteger(((_1405_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1425_outVar;
              _1425_outVar = DCOMP.__default.escapeName((((_1405_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
              generated = RAST.__default.AssignVar(_1425_outVar, generated);
            } else if (((_1405_maybeOutVars).is_None) || ((new BigInteger(((_1405_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1426_tmpVar;
              _1426_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1427_tmpId;
              _1427_tmpId = RAST.Expr.create_Identifier(_1426_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1426_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1428_outVars;
              _1428_outVars = (_1405_maybeOutVars).dtor_value;
              BigInteger _hi29 = new BigInteger((_1428_outVars).Count);
              for (BigInteger _1429_outI = BigInteger.Zero; _1429_outI < _hi29; _1429_outI++) {
                Dafny.ISequence<Dafny.Rune> _1430_outVar;
                _1430_outVar = DCOMP.__default.escapeName(((_1428_outVars).Select(_1429_outI)));
                RAST._IExpr _1431_rhs;
                _1431_rhs = (_1427_tmpId).Sel(Std.Strings.__default.OfNat(_1429_outI));
                generated = (generated).Then(RAST.__default.AssignVar(_1430_outVar, _1431_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Return) {
          DAST._IExpression _1432_exprDafny = _source58.dtor_expr;
          unmatched58 = false;
          {
            RAST._IExpr _1433_expr;
            DCOMP._IOwnership _1434___v72;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1435_recIdents;
            RAST._IExpr _out160;
            DCOMP._IOwnership _out161;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out162;
            (this).GenExpr(_1432_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out160, out _out161, out _out162);
            _1433_expr = _out160;
            _1434___v72 = _out161;
            _1435_recIdents = _out162;
            readIdents = _1435_recIdents;
            if (isLast) {
              generated = _1433_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1433_expr));
            }
            newEnv = env;
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_EarlyReturn) {
          unmatched58 = false;
          {
            generated = earlyReturn;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Halt) {
          unmatched58 = false;
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched58) {
        DAST._IExpression _1436_e = _source58.dtor_Print_a0;
        unmatched58 = false;
        {
          RAST._IExpr _1437_printedExpr;
          DCOMP._IOwnership _1438_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1439_recIdents;
          RAST._IExpr _out163;
          DCOMP._IOwnership _out164;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out165;
          (this).GenExpr(_1436_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out163, out _out164, out _out165);
          _1437_printedExpr = _out163;
          _1438_recOwnership = _out164;
          _1439_recIdents = _out165;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1437_printedExpr)));
          readIdents = _1439_recIdents;
          newEnv = env;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source62 = range;
      bool unmatched62 = true;
      if (unmatched62) {
        if (_source62.is_NoRange) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      if (unmatched62) {
        if (_source62.is_U8) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      if (unmatched62) {
        if (_source62.is_U16) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      if (unmatched62) {
        if (_source62.is_U32) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      if (unmatched62) {
        if (_source62.is_U64) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      if (unmatched62) {
        if (_source62.is_U128) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      if (unmatched62) {
        if (_source62.is_I8) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      if (unmatched62) {
        if (_source62.is_I16) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      if (unmatched62) {
        if (_source62.is_I32) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      if (unmatched62) {
        if (_source62.is_I64) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      if (unmatched62) {
        if (_source62.is_I128) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
        }
      }
      if (unmatched62) {
        DAST._INewtypeRange _1440___v73 = _source62;
        unmatched62 = false;
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
        RAST._IExpr _out166;
        DCOMP._IOwnership _out167;
        DCOMP.COMP.FromOwned(r, expectedOwnership, out _out166, out _out167);
        @out = _out166;
        resultingOwnership = _out167;
        return ;
      } else if (object.Equals(ownership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        RAST._IExpr _out168;
        DCOMP._IOwnership _out169;
        DCOMP.COMP.FromOwned(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), r, DAST.Format.UnaryOpFormat.create_NoFormat()), expectedOwnership, out _out168, out _out169);
        @out = _out168;
        resultingOwnership = _out169;
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
      DAST._IExpression _source63 = e;
      bool unmatched63 = true;
      if (unmatched63) {
        if (_source63.is_Literal) {
          DAST._ILiteral _h140 = _source63.dtor_Literal_a0;
          if (_h140.is_BoolLiteral) {
            bool _1441_b = _h140.dtor_BoolLiteral_a0;
            unmatched63 = false;
            {
              RAST._IExpr _out170;
              DCOMP._IOwnership _out171;
              DCOMP.COMP.FromOwned(RAST.Expr.create_LiteralBool(_1441_b), expectedOwnership, out _out170, out _out171);
              r = _out170;
              resultingOwnership = _out171;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Literal) {
          DAST._ILiteral _h141 = _source63.dtor_Literal_a0;
          if (_h141.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1442_i = _h141.dtor_IntLiteral_a0;
            DAST._IType _1443_t = _h141.dtor_IntLiteral_a1;
            unmatched63 = false;
            {
              DAST._IType _source64 = _1443_t;
              bool unmatched64 = true;
              if (unmatched64) {
                if (_source64.is_Primitive) {
                  DAST._IPrimitive _h80 = _source64.dtor_Primitive_a0;
                  if (_h80.is_Int) {
                    unmatched64 = false;
                    {
                      if ((new BigInteger((_1442_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1442_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1442_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched64) {
                DAST._IType _1444_o = _source64;
                unmatched64 = false;
                {
                  RAST._IType _1445_genType;
                  RAST._IType _out172;
                  _out172 = (this).GenType(_1444_o, false, false);
                  _1445_genType = _out172;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1442_i), _1445_genType);
                }
              }
              RAST._IExpr _out173;
              DCOMP._IOwnership _out174;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out173, out _out174);
              r = _out173;
              resultingOwnership = _out174;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Literal) {
          DAST._ILiteral _h142 = _source63.dtor_Literal_a0;
          if (_h142.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1446_n = _h142.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1447_d = _h142.dtor_DecLiteral_a1;
            DAST._IType _1448_t = _h142.dtor_DecLiteral_a2;
            unmatched63 = false;
            {
              DAST._IType _source65 = _1448_t;
              bool unmatched65 = true;
              if (unmatched65) {
                if (_source65.is_Primitive) {
                  DAST._IPrimitive _h81 = _source65.dtor_Primitive_a0;
                  if (_h81.is_Real) {
                    unmatched65 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1446_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1447_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched65) {
                DAST._IType _1449_o = _source65;
                unmatched65 = false;
                {
                  RAST._IType _1450_genType;
                  RAST._IType _out175;
                  _out175 = (this).GenType(_1449_o, false, false);
                  _1450_genType = _out175;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1446_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1447_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1450_genType);
                }
              }
              RAST._IExpr _out176;
              DCOMP._IOwnership _out177;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out176, out _out177);
              r = _out176;
              resultingOwnership = _out177;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Literal) {
          DAST._ILiteral _h143 = _source63.dtor_Literal_a0;
          if (_h143.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1451_l = _h143.dtor_StringLiteral_a0;
            bool _1452_verbatim = _h143.dtor_verbatim;
            unmatched63 = false;
            {
              if (_1452_verbatim) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Verbatim strings prefixed by @ not supported yet."));
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1451_l, false, _1452_verbatim));
              RAST._IExpr _out178;
              DCOMP._IOwnership _out179;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out178, out _out179);
              r = _out178;
              resultingOwnership = _out179;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Literal) {
          DAST._ILiteral _h144 = _source63.dtor_Literal_a0;
          if (_h144.is_CharLiteralUTF16) {
            BigInteger _1453_c = _h144.dtor_CharLiteralUTF16_a0;
            unmatched63 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1453_c));
              r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
              RAST._IExpr _out180;
              DCOMP._IOwnership _out181;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out180, out _out181);
              r = _out180;
              resultingOwnership = _out181;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Literal) {
          DAST._ILiteral _h145 = _source63.dtor_Literal_a0;
          if (_h145.is_CharLiteral) {
            Dafny.Rune _1454_c = _h145.dtor_CharLiteral_a0;
            unmatched63 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1454_c).Value)));
              if (!((this).UnicodeChars)) {
                r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              } else {
                r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
              RAST._IExpr _out182;
              DCOMP._IOwnership _out183;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out182, out _out183);
              r = _out182;
              resultingOwnership = _out183;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched63) {
        DAST._ILiteral _h146 = _source63.dtor_Literal_a0;
        DAST._IType _1455_tpe = _h146.dtor_Null_a0;
        unmatched63 = false;
        {
          RAST._IType _1456_tpeGen;
          RAST._IType _out184;
          _out184 = (this).GenType(_1455_tpe, false, false);
          _1456_tpeGen = _out184;
          r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None")), _1456_tpeGen);
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
    public void GenExprBinary(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs52 = e;
      DAST._IBinOp _1457_op = _let_tmp_rhs52.dtor_op;
      DAST._IExpression _1458_lExpr = _let_tmp_rhs52.dtor_left;
      DAST._IExpression _1459_rExpr = _let_tmp_rhs52.dtor_right;
      DAST.Format._IBinaryOpFormat _1460_format = _let_tmp_rhs52.dtor_format2;
      bool _1461_becomesLeftCallsRight;
      _1461_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source66 = _1457_op;
        bool unmatched66 = true;
        if (unmatched66) {
          bool disjunctiveMatch11 = false;
          if (_source66.is_SetMerge) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_SetSubtraction) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_SetIntersection) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_SetDisjoint) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_MapMerge) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_MapSubtraction) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_MultisetMerge) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_MultisetSubtraction) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_MultisetIntersection) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_MultisetDisjoint) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_Concat) {
            disjunctiveMatch11 = true;
          }
          if (disjunctiveMatch11) {
            unmatched66 = false;
            return true;
          }
        }
        if (unmatched66) {
          DAST._IBinOp _1462___v74 = _source66;
          unmatched66 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1463_becomesRightCallsLeft;
      _1463_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source67 = _1457_op;
        bool unmatched67 = true;
        if (unmatched67) {
          if (_source67.is_In) {
            unmatched67 = false;
            return true;
          }
        }
        if (unmatched67) {
          DAST._IBinOp _1464___v75 = _source67;
          unmatched67 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1465_becomesCallLeftRight;
      _1465_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source68 = _1457_op;
        bool unmatched68 = true;
        if (unmatched68) {
          if (_source68.is_Eq) {
            bool referential0 = _source68.dtor_referential;
            if ((referential0) == (true)) {
              bool nullable0 = _source68.dtor_nullable;
              if ((nullable0) == (false)) {
                unmatched68 = false;
                return true;
              }
            }
          }
        }
        if (unmatched68) {
          if (_source68.is_SetMerge) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_SetSubtraction) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_SetIntersection) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_SetDisjoint) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_MapMerge) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_MapSubtraction) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_MultisetMerge) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_MultisetSubtraction) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_MultisetIntersection) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_MultisetDisjoint) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_Concat) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          DAST._IBinOp _1466___v76 = _source68;
          unmatched68 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      DCOMP._IOwnership _1467_expectedLeftOwnership;
      _1467_expectedLeftOwnership = ((_1461_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1463_becomesRightCallsLeft) || (_1465_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1468_expectedRightOwnership;
      _1468_expectedRightOwnership = (((_1461_becomesLeftCallsRight) || (_1465_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1463_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1469_left;
      DCOMP._IOwnership _1470___v77;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1471_recIdentsL;
      RAST._IExpr _out187;
      DCOMP._IOwnership _out188;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out189;
      (this).GenExpr(_1458_lExpr, selfIdent, env, _1467_expectedLeftOwnership, out _out187, out _out188, out _out189);
      _1469_left = _out187;
      _1470___v77 = _out188;
      _1471_recIdentsL = _out189;
      RAST._IExpr _1472_right;
      DCOMP._IOwnership _1473___v78;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1474_recIdentsR;
      RAST._IExpr _out190;
      DCOMP._IOwnership _out191;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out192;
      (this).GenExpr(_1459_rExpr, selfIdent, env, _1468_expectedRightOwnership, out _out190, out _out191, out _out192);
      _1472_right = _out190;
      _1473___v78 = _out191;
      _1474_recIdentsR = _out192;
      DAST._IBinOp _source69 = _1457_op;
      bool unmatched69 = true;
      if (unmatched69) {
        if (_source69.is_In) {
          unmatched69 = false;
          {
            r = ((_1472_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1469_left);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_SeqProperPrefix) {
          unmatched69 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1469_left, _1472_right, _1460_format);
        }
      }
      if (unmatched69) {
        if (_source69.is_SeqPrefix) {
          unmatched69 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1469_left, _1472_right, _1460_format);
        }
      }
      if (unmatched69) {
        if (_source69.is_SetMerge) {
          unmatched69 = false;
          {
            r = ((_1469_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1472_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_SetSubtraction) {
          unmatched69 = false;
          {
            r = ((_1469_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1472_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_SetIntersection) {
          unmatched69 = false;
          {
            r = ((_1469_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1472_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_Subset) {
          unmatched69 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1469_left, _1472_right, _1460_format);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_ProperSubset) {
          unmatched69 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1469_left, _1472_right, _1460_format);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_SetDisjoint) {
          unmatched69 = false;
          {
            r = ((_1469_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1472_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_MapMerge) {
          unmatched69 = false;
          {
            r = ((_1469_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1472_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_MapSubtraction) {
          unmatched69 = false;
          {
            r = ((_1469_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1472_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_MultisetMerge) {
          unmatched69 = false;
          {
            r = ((_1469_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1472_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_MultisetSubtraction) {
          unmatched69 = false;
          {
            r = ((_1469_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1472_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_MultisetIntersection) {
          unmatched69 = false;
          {
            r = ((_1469_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1472_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_Submultiset) {
          unmatched69 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1469_left, _1472_right, _1460_format);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_ProperSubmultiset) {
          unmatched69 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1469_left, _1472_right, _1460_format);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_MultisetDisjoint) {
          unmatched69 = false;
          {
            r = ((_1469_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1472_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_Concat) {
          unmatched69 = false;
          {
            r = ((_1469_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1472_right);
          }
        }
      }
      if (unmatched69) {
        DAST._IBinOp _1475___v79 = _source69;
        unmatched69 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1457_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1457_op), _1469_left, _1472_right, _1460_format);
          } else {
            DAST._IBinOp _source70 = _1457_op;
            bool unmatched70 = true;
            if (unmatched70) {
              if (_source70.is_Eq) {
                bool _1476_referential = _source70.dtor_referential;
                bool _1477_nullable = _source70.dtor_nullable;
                unmatched70 = false;
                {
                  if (_1476_referential) {
                    if (_1477_nullable) {
                      r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1469_left, _1472_right));
                    } else {
                      r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1469_left, _1472_right));
                    }
                  } else {
                    r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1469_left, _1472_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                  }
                }
              }
            }
            if (unmatched70) {
              if (_source70.is_EuclidianDiv) {
                unmatched70 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1469_left, _1472_right));
                }
              }
            }
            if (unmatched70) {
              if (_source70.is_EuclidianMod) {
                unmatched70 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1469_left, _1472_right));
                }
              }
            }
            if (unmatched70) {
              Dafny.ISequence<Dafny.Rune> _1478_op = _source70.dtor_Passthrough_a0;
              unmatched70 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1478_op, _1469_left, _1472_right, _1460_format);
              }
            }
          }
        }
      }
      RAST._IExpr _out193;
      DCOMP._IOwnership _out194;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out193, out _out194);
      r = _out193;
      resultingOwnership = _out194;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1471_recIdentsL, _1474_recIdentsR);
      return ;
    }
    public void GenExprConvertFromNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs53 = e;
      DAST._IExpression _1479_expr = _let_tmp_rhs53.dtor_value;
      DAST._IType _1480_fromTpe = _let_tmp_rhs53.dtor_from;
      DAST._IType _1481_toTpe = _let_tmp_rhs53.dtor_typ;
      RAST._IExpr _1482_recursiveGen;
      DCOMP._IOwnership _1483_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1484_recIdents;
      RAST._IExpr _out195;
      DCOMP._IOwnership _out196;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out197;
      (this).GenExpr(_1479_expr, selfIdent, env, expectedOwnership, out _out195, out _out196, out _out197);
      _1482_recursiveGen = _out195;
      _1483_recOwned = _out196;
      _1484_recIdents = _out197;
      r = _1482_recursiveGen;
      if (object.Equals(_1483_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      RAST._IExpr _out198;
      DCOMP._IOwnership _out199;
      DCOMP.COMP.FromOwnership(r, _1483_recOwned, expectedOwnership, out _out198, out _out199);
      r = _out198;
      resultingOwnership = _out199;
      readIdents = _1484_recIdents;
    }
    public void GenExprConvertToNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IExpression _1485_expr = _let_tmp_rhs54.dtor_value;
      DAST._IType _1486_fromTpe = _let_tmp_rhs54.dtor_from;
      DAST._IType _1487_toTpe = _let_tmp_rhs54.dtor_typ;
      RAST._IExpr _1488_recursiveGen;
      DCOMP._IOwnership _1489_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1490_recIdents;
      RAST._IExpr _out200;
      DCOMP._IOwnership _out201;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out202;
      (this).GenExpr(_1485_expr, selfIdent, env, expectedOwnership, out _out200, out _out201, out _out202);
      _1488_recursiveGen = _out200;
      _1489_recOwned = _out201;
      _1490_recIdents = _out202;
      r = _1488_recursiveGen;
      if (object.Equals(_1489_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
      RAST._IExpr _out203;
      DCOMP._IOwnership _out204;
      DCOMP.COMP.FromOwnership(r, _1489_recOwned, expectedOwnership, out _out203, out _out204);
      r = _out203;
      resultingOwnership = _out204;
      readIdents = _1490_recIdents;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _1491_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _1492_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _1493_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _1493_toTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1494___v80 = _let_tmp_rhs56.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _1495___v81 = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      DAST._IType _1496_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _1497_range = _let_tmp_rhs57.dtor_range;
      bool _1498_erase = _let_tmp_rhs57.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1499_attributes = _let_tmp_rhs57.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _1500_nativeToType;
      _1500_nativeToType = DCOMP.COMP.NewtypeToRustType(_1496_b, _1497_range);
      if (object.Equals(_1492_fromTpe, _1496_b)) {
        RAST._IExpr _1501_recursiveGen;
        DCOMP._IOwnership _1502_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1503_recIdents;
        RAST._IExpr _out205;
        DCOMP._IOwnership _out206;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out207;
        (this).GenExpr(_1491_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out205, out _out206, out _out207);
        _1501_recursiveGen = _out205;
        _1502_recOwned = _out206;
        _1503_recIdents = _out207;
        readIdents = _1503_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source71 = _1500_nativeToType;
        bool unmatched71 = true;
        if (unmatched71) {
          if (_source71.is_Some) {
            RAST._IType _1504_v = _source71.dtor_value;
            unmatched71 = false;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1501_recursiveGen, RAST.Expr.create_ExprFromType(_1504_v)));
            RAST._IExpr _out208;
            DCOMP._IOwnership _out209;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out208, out _out209);
            r = _out208;
            resultingOwnership = _out209;
          }
        }
        if (unmatched71) {
          unmatched71 = false;
          if (_1498_erase) {
            r = _1501_recursiveGen;
          } else {
            RAST._IType _1505_rhsType;
            RAST._IType _out210;
            _out210 = (this).GenType(_1493_toTpe, true, false);
            _1505_rhsType = _out210;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1505_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1501_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out211;
          DCOMP._IOwnership _out212;
          DCOMP.COMP.FromOwnership(r, _1502_recOwned, expectedOwnership, out _out211, out _out212);
          r = _out211;
          resultingOwnership = _out212;
        }
      } else {
        RAST._IExpr _out213;
        DCOMP._IOwnership _out214;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out215;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1491_expr, _1492_fromTpe, _1496_b), _1496_b, _1493_toTpe), selfIdent, env, expectedOwnership, out _out213, out _out214, out _out215);
        r = _out213;
        resultingOwnership = _out214;
        readIdents = _out215;
      }
    }
    public void GenExprConvertFromNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs58 = e;
      DAST._IExpression _1506_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _1507_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _1508_toTpe = _let_tmp_rhs58.dtor_typ;
      DAST._IType _let_tmp_rhs59 = _1507_fromTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1509___v82 = _let_tmp_rhs59.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _1510___v83 = _let_tmp_rhs59.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs60 = _let_tmp_rhs59.dtor_resolved;
      DAST._IType _1511_b = _let_tmp_rhs60.dtor_baseType;
      DAST._INewtypeRange _1512_range = _let_tmp_rhs60.dtor_range;
      bool _1513_erase = _let_tmp_rhs60.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1514_attributes = _let_tmp_rhs60.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _1515_nativeFromType;
      _1515_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1511_b, _1512_range);
      if (object.Equals(_1511_b, _1508_toTpe)) {
        RAST._IExpr _1516_recursiveGen;
        DCOMP._IOwnership _1517_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1518_recIdents;
        RAST._IExpr _out216;
        DCOMP._IOwnership _out217;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out218;
        (this).GenExpr(_1506_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out216, out _out217, out _out218);
        _1516_recursiveGen = _out216;
        _1517_recOwned = _out217;
        _1518_recIdents = _out218;
        readIdents = _1518_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source72 = _1515_nativeFromType;
        bool unmatched72 = true;
        if (unmatched72) {
          if (_source72.is_Some) {
            RAST._IType _1519_v = _source72.dtor_value;
            unmatched72 = false;
            RAST._IType _1520_toTpeRust;
            RAST._IType _out219;
            _out219 = (this).GenType(_1508_toTpe, false, false);
            _1520_toTpeRust = _out219;
            r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1520_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1516_recursiveGen));
            RAST._IExpr _out220;
            DCOMP._IOwnership _out221;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out220, out _out221);
            r = _out220;
            resultingOwnership = _out221;
          }
        }
        if (unmatched72) {
          unmatched72 = false;
          if (_1513_erase) {
            r = _1516_recursiveGen;
          } else {
            r = (_1516_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out222;
          DCOMP._IOwnership _out223;
          DCOMP.COMP.FromOwnership(r, _1517_recOwned, expectedOwnership, out _out222, out _out223);
          r = _out222;
          resultingOwnership = _out223;
        }
      } else {
        if ((_1515_nativeFromType).is_Some) {
          if (object.Equals(_1508_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1521_recursiveGen;
            DCOMP._IOwnership _1522_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1523_recIdents;
            RAST._IExpr _out224;
            DCOMP._IOwnership _out225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out226;
            (this).GenExpr(_1506_expr, selfIdent, env, expectedOwnership, out _out224, out _out225, out _out226);
            _1521_recursiveGen = _out224;
            _1522_recOwned = _out225;
            _1523_recIdents = _out226;
            RAST._IExpr _out227;
            DCOMP._IOwnership _out228;
            DCOMP.COMP.FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1521_recursiveGen, (this).DafnyCharUnderlying)), _1522_recOwned, expectedOwnership, out _out227, out _out228);
            r = _out227;
            resultingOwnership = _out228;
            readIdents = _1523_recIdents;
            return ;
          }
        }
        RAST._IExpr _out229;
        DCOMP._IOwnership _out230;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out231;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1506_expr, _1507_fromTpe, _1511_b), _1511_b, _1508_toTpe), selfIdent, env, expectedOwnership, out _out229, out _out230, out _out231);
        r = _out229;
        resultingOwnership = _out230;
        readIdents = _out231;
      }
    }
    public void GenExprConvertNotImplemented(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs61 = e;
      DAST._IExpression _1524_expr = _let_tmp_rhs61.dtor_value;
      DAST._IType _1525_fromTpe = _let_tmp_rhs61.dtor_from;
      DAST._IType _1526_toTpe = _let_tmp_rhs61.dtor_typ;
      RAST._IType _1527_fromTpeGen;
      RAST._IType _out232;
      _out232 = (this).GenType(_1525_fromTpe, true, false);
      _1527_fromTpeGen = _out232;
      RAST._IType _1528_toTpeGen;
      RAST._IType _out233;
      _out233 = (this).GenType(_1526_toTpe, true, false);
      _1528_toTpeGen = _out233;
      RAST._IExpr _1529_recursiveGen;
      DCOMP._IOwnership _1530_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1531_recIdents;
      RAST._IExpr _out234;
      DCOMP._IOwnership _out235;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out236;
      (this).GenExpr(_1524_expr, selfIdent, env, expectedOwnership, out _out234, out _out235, out _out236);
      _1529_recursiveGen = _out234;
      _1530_recOwned = _out235;
      _1531_recIdents = _out236;
      Dafny.ISequence<Dafny.Rune> _1532_msg;
      _1532_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1527_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1528_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1532_msg);
      r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1529_recursiveGen)._ToString(DCOMP.__default.IND), _1532_msg));
      RAST._IExpr _out237;
      DCOMP._IOwnership _out238;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out237, out _out238);
      r = _out237;
      resultingOwnership = _out238;
      readIdents = _1531_recIdents;
    }
    public void GenExprConvert(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs62 = e;
      DAST._IExpression _1533_expr = _let_tmp_rhs62.dtor_value;
      DAST._IType _1534_fromTpe = _let_tmp_rhs62.dtor_from;
      DAST._IType _1535_toTpe = _let_tmp_rhs62.dtor_typ;
      if (object.Equals(_1534_fromTpe, _1535_toTpe)) {
        RAST._IExpr _1536_recursiveGen;
        DCOMP._IOwnership _1537_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1538_recIdents;
        RAST._IExpr _out239;
        DCOMP._IOwnership _out240;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out241;
        (this).GenExpr(_1533_expr, selfIdent, env, expectedOwnership, out _out239, out _out240, out _out241);
        _1536_recursiveGen = _out239;
        _1537_recOwned = _out240;
        _1538_recIdents = _out241;
        r = _1536_recursiveGen;
        RAST._IExpr _out242;
        DCOMP._IOwnership _out243;
        DCOMP.COMP.FromOwnership(r, _1537_recOwned, expectedOwnership, out _out242, out _out243);
        r = _out242;
        resultingOwnership = _out243;
        readIdents = _1538_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source73 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1534_fromTpe, _1535_toTpe);
        bool unmatched73 = true;
        if (unmatched73) {
          DAST._IType _01 = _source73.dtor__0;
          if (_01.is_Nullable) {
            DAST._IType _1539___v84 = _01.dtor_Nullable_a0;
            DAST._IType _1540___v85 = _source73.dtor__1;
            unmatched73 = false;
            {
              RAST._IExpr _out244;
              DCOMP._IOwnership _out245;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out246;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out244, out _out245, out _out246);
              r = _out244;
              resultingOwnership = _out245;
              readIdents = _out246;
            }
          }
        }
        if (unmatched73) {
          DAST._IType _1541___v86 = _source73.dtor__0;
          DAST._IType _11 = _source73.dtor__1;
          if (_11.is_Nullable) {
            DAST._IType _1542___v87 = _11.dtor_Nullable_a0;
            unmatched73 = false;
            {
              RAST._IExpr _out247;
              DCOMP._IOwnership _out248;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out249;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out247, out _out248, out _out249);
              r = _out247;
              resultingOwnership = _out248;
              readIdents = _out249;
            }
          }
        }
        if (unmatched73) {
          DAST._IType _1543___v88 = _source73.dtor__0;
          DAST._IType _12 = _source73.dtor__1;
          if (_12.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1544___v89 = _12.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1545___v90 = _12.dtor_typeArgs;
            DAST._IResolvedType resolved1 = _12.dtor_resolved;
            if (resolved1.is_Newtype) {
              DAST._IType _1546_b = resolved1.dtor_baseType;
              DAST._INewtypeRange _1547_range = resolved1.dtor_range;
              bool _1548_erase = resolved1.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1549_attributes = resolved1.dtor_attributes;
              unmatched73 = false;
              {
                RAST._IExpr _out250;
                DCOMP._IOwnership _out251;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out252;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out250, out _out251, out _out252);
                r = _out250;
                resultingOwnership = _out251;
                readIdents = _out252;
              }
            }
          }
        }
        if (unmatched73) {
          DAST._IType _02 = _source73.dtor__0;
          if (_02.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1550___v91 = _02.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1551___v92 = _02.dtor_typeArgs;
            DAST._IResolvedType resolved2 = _02.dtor_resolved;
            if (resolved2.is_Newtype) {
              DAST._IType _1552_b = resolved2.dtor_baseType;
              DAST._INewtypeRange _1553_range = resolved2.dtor_range;
              bool _1554_erase = resolved2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1555_attributes = resolved2.dtor_attributes;
              DAST._IType _1556___v93 = _source73.dtor__1;
              unmatched73 = false;
              {
                RAST._IExpr _out253;
                DCOMP._IOwnership _out254;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out255;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out253, out _out254, out _out255);
                r = _out253;
                resultingOwnership = _out254;
                readIdents = _out255;
              }
            }
          }
        }
        if (unmatched73) {
          DAST._IType _03 = _source73.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h82 = _03.dtor_Primitive_a0;
            if (_h82.is_Int) {
              DAST._IType _13 = _source73.dtor__1;
              if (_13.is_Primitive) {
                DAST._IPrimitive _h83 = _13.dtor_Primitive_a0;
                if (_h83.is_Real) {
                  unmatched73 = false;
                  {
                    RAST._IExpr _1557_recursiveGen;
                    DCOMP._IOwnership _1558___v94;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1559_recIdents;
                    RAST._IExpr _out256;
                    DCOMP._IOwnership _out257;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out258;
                    (this).GenExpr(_1533_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out256, out _out257, out _out258);
                    _1557_recursiveGen = _out256;
                    _1558___v94 = _out257;
                    _1559_recIdents = _out258;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1557_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out259;
                    DCOMP._IOwnership _out260;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out259, out _out260);
                    r = _out259;
                    resultingOwnership = _out260;
                    readIdents = _1559_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched73) {
          DAST._IType _04 = _source73.dtor__0;
          if (_04.is_Primitive) {
            DAST._IPrimitive _h84 = _04.dtor_Primitive_a0;
            if (_h84.is_Real) {
              DAST._IType _14 = _source73.dtor__1;
              if (_14.is_Primitive) {
                DAST._IPrimitive _h85 = _14.dtor_Primitive_a0;
                if (_h85.is_Int) {
                  unmatched73 = false;
                  {
                    RAST._IExpr _1560_recursiveGen;
                    DCOMP._IOwnership _1561___v95;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1562_recIdents;
                    RAST._IExpr _out261;
                    DCOMP._IOwnership _out262;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out263;
                    (this).GenExpr(_1533_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out261, out _out262, out _out263);
                    _1560_recursiveGen = _out261;
                    _1561___v95 = _out262;
                    _1562_recIdents = _out263;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1560_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out264;
                    DCOMP._IOwnership _out265;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out264, out _out265);
                    r = _out264;
                    resultingOwnership = _out265;
                    readIdents = _1562_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched73) {
          DAST._IType _05 = _source73.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h86 = _05.dtor_Primitive_a0;
            if (_h86.is_Int) {
              DAST._IType _15 = _source73.dtor__1;
              if (_15.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1563___v96 = _15.dtor_Passthrough_a0;
                unmatched73 = false;
                {
                  RAST._IType _1564_rhsType;
                  RAST._IType _out266;
                  _out266 = (this).GenType(_1535_toTpe, true, false);
                  _1564_rhsType = _out266;
                  RAST._IExpr _1565_recursiveGen;
                  DCOMP._IOwnership _1566___v97;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1567_recIdents;
                  RAST._IExpr _out267;
                  DCOMP._IOwnership _out268;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out269;
                  (this).GenExpr(_1533_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out267, out _out268, out _out269);
                  _1565_recursiveGen = _out267;
                  _1566___v97 = _out268;
                  _1567_recIdents = _out269;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1564_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1565_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out270;
                  DCOMP._IOwnership _out271;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out270, out _out271);
                  r = _out270;
                  resultingOwnership = _out271;
                  readIdents = _1567_recIdents;
                }
              }
            }
          }
        }
        if (unmatched73) {
          DAST._IType _06 = _source73.dtor__0;
          if (_06.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1568___v98 = _06.dtor_Passthrough_a0;
            DAST._IType _16 = _source73.dtor__1;
            if (_16.is_Primitive) {
              DAST._IPrimitive _h87 = _16.dtor_Primitive_a0;
              if (_h87.is_Int) {
                unmatched73 = false;
                {
                  RAST._IType _1569_rhsType;
                  RAST._IType _out272;
                  _out272 = (this).GenType(_1534_fromTpe, true, false);
                  _1569_rhsType = _out272;
                  RAST._IExpr _1570_recursiveGen;
                  DCOMP._IOwnership _1571___v99;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1572_recIdents;
                  RAST._IExpr _out273;
                  DCOMP._IOwnership _out274;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out275;
                  (this).GenExpr(_1533_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out273, out _out274, out _out275);
                  _1570_recursiveGen = _out273;
                  _1571___v99 = _out274;
                  _1572_recIdents = _out275;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::dafny_runtime::BigInt::from("), (_1570_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")}")));
                  RAST._IExpr _out276;
                  DCOMP._IOwnership _out277;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out276, out _out277);
                  r = _out276;
                  resultingOwnership = _out277;
                  readIdents = _1572_recIdents;
                }
              }
            }
          }
        }
        if (unmatched73) {
          DAST._IType _07 = _source73.dtor__0;
          if (_07.is_Primitive) {
            DAST._IPrimitive _h88 = _07.dtor_Primitive_a0;
            if (_h88.is_Int) {
              DAST._IType _17 = _source73.dtor__1;
              if (_17.is_Primitive) {
                DAST._IPrimitive _h89 = _17.dtor_Primitive_a0;
                if (_h89.is_Char) {
                  unmatched73 = false;
                  {
                    RAST._IType _1573_rhsType;
                    RAST._IType _out278;
                    _out278 = (this).GenType(_1535_toTpe, true, false);
                    _1573_rhsType = _out278;
                    RAST._IExpr _1574_recursiveGen;
                    DCOMP._IOwnership _1575___v100;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1576_recIdents;
                    RAST._IExpr _out279;
                    DCOMP._IOwnership _out280;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out281;
                    (this).GenExpr(_1533_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out279, out _out280, out _out281);
                    _1574_recursiveGen = _out279;
                    _1575___v100 = _out280;
                    _1576_recIdents = _out281;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), (_1574_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()")));
                    RAST._IExpr _out282;
                    DCOMP._IOwnership _out283;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out282, out _out283);
                    r = _out282;
                    resultingOwnership = _out283;
                    readIdents = _1576_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched73) {
          DAST._IType _08 = _source73.dtor__0;
          if (_08.is_Primitive) {
            DAST._IPrimitive _h810 = _08.dtor_Primitive_a0;
            if (_h810.is_Char) {
              DAST._IType _18 = _source73.dtor__1;
              if (_18.is_Primitive) {
                DAST._IPrimitive _h811 = _18.dtor_Primitive_a0;
                if (_h811.is_Int) {
                  unmatched73 = false;
                  {
                    RAST._IType _1577_rhsType;
                    RAST._IType _out284;
                    _out284 = (this).GenType(_1534_fromTpe, true, false);
                    _1577_rhsType = _out284;
                    RAST._IExpr _1578_recursiveGen;
                    DCOMP._IOwnership _1579___v101;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1580_recIdents;
                    RAST._IExpr _out285;
                    DCOMP._IOwnership _out286;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out287;
                    (this).GenExpr(_1533_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out285, out _out286, out _out287);
                    _1578_recursiveGen = _out285;
                    _1579___v101 = _out286;
                    _1580_recIdents = _out287;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1578_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out288;
                    DCOMP._IOwnership _out289;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out288, out _out289);
                    r = _out288;
                    resultingOwnership = _out289;
                    readIdents = _1580_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched73) {
          DAST._IType _09 = _source73.dtor__0;
          if (_09.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1581___v102 = _09.dtor_Passthrough_a0;
            DAST._IType _19 = _source73.dtor__1;
            if (_19.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1582___v103 = _19.dtor_Passthrough_a0;
              unmatched73 = false;
              {
                RAST._IExpr _1583_recursiveGen;
                DCOMP._IOwnership _1584___v104;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1585_recIdents;
                RAST._IExpr _out290;
                DCOMP._IOwnership _out291;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out292;
                (this).GenExpr(_1533_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out290, out _out291, out _out292);
                _1583_recursiveGen = _out290;
                _1584___v104 = _out291;
                _1585_recIdents = _out292;
                RAST._IType _1586_toTpeGen;
                RAST._IType _out293;
                _out293 = (this).GenType(_1535_toTpe, true, false);
                _1586_toTpeGen = _out293;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1583_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1586_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out294;
                DCOMP._IOwnership _out295;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out294, out _out295);
                r = _out294;
                resultingOwnership = _out295;
                readIdents = _1585_recIdents;
              }
            }
          }
        }
        if (unmatched73) {
          _System._ITuple2<DAST._IType, DAST._IType> _1587___v105 = _source73;
          unmatched73 = false;
          {
            RAST._IExpr _out296;
            DCOMP._IOwnership _out297;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out298;
            (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out296, out _out297, out _out298);
            r = _out296;
            resultingOwnership = _out297;
            readIdents = _out298;
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
      Std.Wrappers._IOption<RAST._IType> _1588_tpe;
      _1588_tpe = (env).GetType(rName);
      bool _1589_currentlyBorrowed;
      _1589_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1590_noNeedOfClone;
      _1590_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        r = RAST.__default.BorrowMut(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        if (!(_1590_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1590_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1589_currentlyBorrowed) {
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
      DAST._IExpression _source74 = e;
      bool unmatched74 = true;
      if (unmatched74) {
        if (_source74.is_Literal) {
          DAST._ILiteral _1591___v106 = _source74.dtor_Literal_a0;
          unmatched74 = false;
          RAST._IExpr _out299;
          DCOMP._IOwnership _out300;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out301;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out299, out _out300, out _out301);
          r = _out299;
          resultingOwnership = _out300;
          readIdents = _out301;
        }
      }
      if (unmatched74) {
        if (_source74.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1592_name = _source74.dtor_Ident_a0;
          unmatched74 = false;
          {
            RAST._IExpr _out302;
            DCOMP._IOwnership _out303;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out304;
            (this).GenIdent(DCOMP.__default.escapeName(_1592_name), selfIdent, env, expectedOwnership, out _out302, out _out303, out _out304);
            r = _out302;
            resultingOwnership = _out303;
            readIdents = _out304;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1593_path = _source74.dtor_Companion_a0;
          unmatched74 = false;
          {
            RAST._IExpr _out305;
            _out305 = DCOMP.COMP.GenPathExpr(_1593_path);
            r = _out305;
            if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else {
              RAST._IExpr _out306;
              DCOMP._IOwnership _out307;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out306, out _out307);
              r = _out306;
              resultingOwnership = _out307;
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_InitializationValue) {
          DAST._IType _1594_typ = _source74.dtor_typ;
          unmatched74 = false;
          {
            RAST._IType _1595_typExpr;
            RAST._IType _out308;
            _out308 = (this).GenType(_1594_typ, false, false);
            _1595_typExpr = _out308;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1595_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
            RAST._IExpr _out309;
            DCOMP._IOwnership _out310;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out309, out _out310);
            r = _out309;
            resultingOwnership = _out310;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _1596_values = _source74.dtor_Tuple_a0;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1597_exprs;
            _1597_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi30 = new BigInteger((_1596_values).Count);
            for (BigInteger _1598_i = BigInteger.Zero; _1598_i < _hi30; _1598_i++) {
              RAST._IExpr _1599_recursiveGen;
              DCOMP._IOwnership _1600___v107;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1601_recIdents;
              RAST._IExpr _out311;
              DCOMP._IOwnership _out312;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out313;
              (this).GenExpr((_1596_values).Select(_1598_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out311, out _out312, out _out313);
              _1599_recursiveGen = _out311;
              _1600___v107 = _out312;
              _1601_recIdents = _out313;
              _1597_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1597_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1599_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1601_recIdents);
            }
            r = (((new BigInteger((_1596_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_1597_exprs)) : (RAST.__default.SystemTuple(_1597_exprs)));
            RAST._IExpr _out314;
            DCOMP._IOwnership _out315;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out314, out _out315);
            r = _out314;
            resultingOwnership = _out315;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1602_path = _source74.dtor_path;
          Dafny.ISequence<DAST._IType> _1603_typeArgs = _source74.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1604_args = _source74.dtor_args;
          unmatched74 = false;
          {
            RAST._IExpr _out316;
            _out316 = DCOMP.COMP.GenPathExpr(_1602_path);
            r = _out316;
            if ((new BigInteger((_1603_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1605_typeExprs;
              _1605_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi31 = new BigInteger((_1603_typeArgs).Count);
              for (BigInteger _1606_i = BigInteger.Zero; _1606_i < _hi31; _1606_i++) {
                RAST._IType _1607_typeExpr;
                RAST._IType _out317;
                _out317 = (this).GenType((_1603_typeArgs).Select(_1606_i), false, false);
                _1607_typeExpr = _out317;
                _1605_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1605_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1607_typeExpr));
              }
              r = (r).ApplyType(_1605_typeExprs);
            }
            r = (r).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1608_arguments;
            _1608_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi32 = new BigInteger((_1604_args).Count);
            for (BigInteger _1609_i = BigInteger.Zero; _1609_i < _hi32; _1609_i++) {
              RAST._IExpr _1610_recursiveGen;
              DCOMP._IOwnership _1611___v108;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1612_recIdents;
              RAST._IExpr _out318;
              DCOMP._IOwnership _out319;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out320;
              (this).GenExpr((_1604_args).Select(_1609_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out318, out _out319, out _out320);
              _1610_recursiveGen = _out318;
              _1611___v108 = _out319;
              _1612_recIdents = _out320;
              _1608_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1608_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1610_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1612_recIdents);
            }
            r = (r).Apply(_1608_arguments);
            RAST._IExpr _out321;
            DCOMP._IOwnership _out322;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out321, out _out322);
            r = _out321;
            resultingOwnership = _out322;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_NewArray) {
          Dafny.ISequence<DAST._IExpression> _1613_dims = _source74.dtor_dims;
          DAST._IType _1614_typ = _source74.dtor_typ;
          unmatched74 = false;
          {
            BigInteger _1615_i;
            _1615_i = (new BigInteger((_1613_dims).Count)) - (BigInteger.One);
            RAST._IType _1616_genTyp;
            RAST._IType _out323;
            _out323 = (this).GenType(_1614_typ, false, false);
            _1616_genTyp = _out323;
            Dafny.ISequence<Dafny.Rune> _1617_s;
            _1617_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1616_genTyp)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::std::default::Default>::default()"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            while ((_1615_i).Sign != -1) {
              RAST._IExpr _1618_recursiveGen;
              DCOMP._IOwnership _1619___v109;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1620_recIdents;
              RAST._IExpr _out324;
              DCOMP._IOwnership _out325;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out326;
              (this).GenExpr((_1613_dims).Select(_1615_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out324, out _out325, out _out326);
              _1618_recursiveGen = _out324;
              _1619___v109 = _out325;
              _1620_recIdents = _out326;
              _1617_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), _1617_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), (_1618_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1620_recIdents);
              _1615_i = (_1615_i) - (BigInteger.One);
            }
            r = RAST.Expr.create_RawExpr(_1617_s);
            RAST._IExpr _out327;
            DCOMP._IOwnership _out328;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out327, out _out328);
            r = _out327;
            resultingOwnership = _out328;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_DatatypeValue) {
          DAST._IDatatypeType _1621_datatypeType = _source74.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1622_typeArgs = _source74.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1623_variant = _source74.dtor_variant;
          bool _1624_isCo = _source74.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1625_values = _source74.dtor_contents;
          unmatched74 = false;
          {
            RAST._IExpr _out329;
            _out329 = DCOMP.COMP.GenPathExpr((_1621_datatypeType).dtor_path);
            r = _out329;
            Dafny.ISequence<RAST._IType> _1626_genTypeArgs;
            _1626_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi33 = new BigInteger((_1622_typeArgs).Count);
            for (BigInteger _1627_i = BigInteger.Zero; _1627_i < _hi33; _1627_i++) {
              RAST._IType _1628_typeExpr;
              RAST._IType _out330;
              _out330 = (this).GenType((_1622_typeArgs).Select(_1627_i), false, false);
              _1628_typeExpr = _out330;
              _1626_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1626_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1628_typeExpr));
            }
            if ((new BigInteger((_1622_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1626_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1623_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1629_assignments;
            _1629_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi34 = new BigInteger((_1625_values).Count);
            for (BigInteger _1630_i = BigInteger.Zero; _1630_i < _hi34; _1630_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs63 = (_1625_values).Select(_1630_i);
              Dafny.ISequence<Dafny.Rune> _1631_name = _let_tmp_rhs63.dtor__0;
              DAST._IExpression _1632_value = _let_tmp_rhs63.dtor__1;
              if (_1624_isCo) {
                RAST._IExpr _1633_recursiveGen;
                DCOMP._IOwnership _1634___v110;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1635_recIdents;
                RAST._IExpr _out331;
                DCOMP._IOwnership _out332;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out333;
                (this).GenExpr(_1632_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out331, out _out332, out _out333);
                _1633_recursiveGen = _out331;
                _1634___v110 = _out332;
                _1635_recIdents = _out333;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1635_recIdents);
                Dafny.ISequence<Dafny.Rune> _1636_allReadCloned;
                _1636_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1635_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1637_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1635_recIdents).Elements) {
                    _1637_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1635_recIdents).Contains(_1637_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 3270)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1636_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1636_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1637_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1637_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1635_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1635_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1637_next));
                }
                Dafny.ISequence<Dafny.Rune> _1638_wasAssigned;
                _1638_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1636_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1633_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1629_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1629_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1631_name, RAST.Expr.create_RawExpr(_1638_wasAssigned))));
              } else {
                RAST._IExpr _1639_recursiveGen;
                DCOMP._IOwnership _1640___v111;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1641_recIdents;
                RAST._IExpr _out334;
                DCOMP._IOwnership _out335;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out336;
                (this).GenExpr(_1632_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out334, out _out335, out _out336);
                _1639_recursiveGen = _out334;
                _1640___v111 = _out335;
                _1641_recIdents = _out336;
                _1629_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1629_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1631_name, _1639_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1641_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1629_assignments);
            if ((this).IsRcWrapped((_1621_datatypeType).dtor_attributes)) {
              r = RAST.__default.RcNew(r);
            }
            RAST._IExpr _out337;
            DCOMP._IOwnership _out338;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out337, out _out338);
            r = _out337;
            resultingOwnership = _out338;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Convert) {
          DAST._IExpression _1642___v112 = _source74.dtor_value;
          DAST._IType _1643___v113 = _source74.dtor_from;
          DAST._IType _1644___v114 = _source74.dtor_typ;
          unmatched74 = false;
          {
            RAST._IExpr _out339;
            DCOMP._IOwnership _out340;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out341;
            (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out339, out _out340, out _out341);
            r = _out339;
            resultingOwnership = _out340;
            readIdents = _out341;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SeqConstruct) {
          DAST._IExpression _1645_length = _source74.dtor_length;
          DAST._IExpression _1646_expr = _source74.dtor_elem;
          unmatched74 = false;
          {
            RAST._IExpr _1647_recursiveGen;
            DCOMP._IOwnership _1648___v115;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1649_recIdents;
            RAST._IExpr _out342;
            DCOMP._IOwnership _out343;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out344;
            (this).GenExpr(_1646_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out342, out _out343, out _out344);
            _1647_recursiveGen = _out342;
            _1648___v115 = _out343;
            _1649_recIdents = _out344;
            RAST._IExpr _1650_lengthGen;
            DCOMP._IOwnership _1651___v116;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1652_lengthIdents;
            RAST._IExpr _out345;
            DCOMP._IOwnership _out346;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out347;
            (this).GenExpr(_1645_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out345, out _out346, out _out347);
            _1650_lengthGen = _out345;
            _1651___v116 = _out346;
            _1652_lengthIdents = _out347;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1647_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1650_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1649_recIdents, _1652_lengthIdents);
            RAST._IExpr _out348;
            DCOMP._IOwnership _out349;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out348, out _out349);
            r = _out348;
            resultingOwnership = _out349;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _1653_exprs = _source74.dtor_elements;
          DAST._IType _1654_typ = _source74.dtor_typ;
          unmatched74 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1655_genTpe;
            RAST._IType _out350;
            _out350 = (this).GenType(_1654_typ, false, false);
            _1655_genTpe = _out350;
            BigInteger _1656_i;
            _1656_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1657_args;
            _1657_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1656_i) < (new BigInteger((_1653_exprs).Count))) {
              RAST._IExpr _1658_recursiveGen;
              DCOMP._IOwnership _1659___v117;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1660_recIdents;
              RAST._IExpr _out351;
              DCOMP._IOwnership _out352;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out353;
              (this).GenExpr((_1653_exprs).Select(_1656_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out351, out _out352, out _out353);
              _1658_recursiveGen = _out351;
              _1659___v117 = _out352;
              _1660_recIdents = _out353;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1660_recIdents);
              _1657_args = Dafny.Sequence<RAST._IExpr>.Concat(_1657_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1658_recursiveGen));
              _1656_i = (_1656_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_1657_args);
            if ((new BigInteger((_1657_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1655_genTpe));
            }
            RAST._IExpr _out354;
            DCOMP._IOwnership _out355;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out354, out _out355);
            r = _out354;
            resultingOwnership = _out355;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _1661_exprs = _source74.dtor_elements;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1662_generatedValues;
            _1662_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1663_i;
            _1663_i = BigInteger.Zero;
            while ((_1663_i) < (new BigInteger((_1661_exprs).Count))) {
              RAST._IExpr _1664_recursiveGen;
              DCOMP._IOwnership _1665___v118;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1666_recIdents;
              RAST._IExpr _out356;
              DCOMP._IOwnership _out357;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out358;
              (this).GenExpr((_1661_exprs).Select(_1663_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out356, out _out357, out _out358);
              _1664_recursiveGen = _out356;
              _1665___v118 = _out357;
              _1666_recIdents = _out358;
              _1662_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1662_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1664_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1666_recIdents);
              _1663_i = (_1663_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_1662_generatedValues);
            RAST._IExpr _out359;
            DCOMP._IOwnership _out360;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out359, out _out360);
            r = _out359;
            resultingOwnership = _out360;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _1667_exprs = _source74.dtor_elements;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1668_generatedValues;
            _1668_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1669_i;
            _1669_i = BigInteger.Zero;
            while ((_1669_i) < (new BigInteger((_1667_exprs).Count))) {
              RAST._IExpr _1670_recursiveGen;
              DCOMP._IOwnership _1671___v119;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1672_recIdents;
              RAST._IExpr _out361;
              DCOMP._IOwnership _out362;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out363;
              (this).GenExpr((_1667_exprs).Select(_1669_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out361, out _out362, out _out363);
              _1670_recursiveGen = _out361;
              _1671___v119 = _out362;
              _1672_recIdents = _out363;
              _1668_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1668_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1670_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1672_recIdents);
              _1669_i = (_1669_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_1668_generatedValues);
            RAST._IExpr _out364;
            DCOMP._IOwnership _out365;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out364, out _out365);
            r = _out364;
            resultingOwnership = _out365;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_ToMultiset) {
          DAST._IExpression _1673_expr = _source74.dtor_ToMultiset_a0;
          unmatched74 = false;
          {
            RAST._IExpr _1674_recursiveGen;
            DCOMP._IOwnership _1675___v120;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1676_recIdents;
            RAST._IExpr _out366;
            DCOMP._IOwnership _out367;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out368;
            (this).GenExpr(_1673_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out366, out _out367, out _out368);
            _1674_recursiveGen = _out366;
            _1675___v120 = _out367;
            _1676_recIdents = _out368;
            r = ((_1674_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _1676_recIdents;
            RAST._IExpr _out369;
            DCOMP._IOwnership _out370;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out369, out _out370);
            r = _out369;
            resultingOwnership = _out370;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1677_mapElems = _source74.dtor_mapElems;
          unmatched74 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1678_generatedValues;
            _1678_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1679_i;
            _1679_i = BigInteger.Zero;
            while ((_1679_i) < (new BigInteger((_1677_mapElems).Count))) {
              RAST._IExpr _1680_recursiveGenKey;
              DCOMP._IOwnership _1681___v121;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1682_recIdentsKey;
              RAST._IExpr _out371;
              DCOMP._IOwnership _out372;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out373;
              (this).GenExpr(((_1677_mapElems).Select(_1679_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out371, out _out372, out _out373);
              _1680_recursiveGenKey = _out371;
              _1681___v121 = _out372;
              _1682_recIdentsKey = _out373;
              RAST._IExpr _1683_recursiveGenValue;
              DCOMP._IOwnership _1684___v122;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1685_recIdentsValue;
              RAST._IExpr _out374;
              DCOMP._IOwnership _out375;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out376;
              (this).GenExpr(((_1677_mapElems).Select(_1679_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out374, out _out375, out _out376);
              _1683_recursiveGenValue = _out374;
              _1684___v122 = _out375;
              _1685_recIdentsValue = _out376;
              _1678_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1678_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1680_recursiveGenKey, _1683_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1682_recIdentsKey), _1685_recIdentsValue);
              _1679_i = (_1679_i) + (BigInteger.One);
            }
            _1679_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1686_arguments;
            _1686_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1679_i) < (new BigInteger((_1678_generatedValues).Count))) {
              RAST._IExpr _1687_genKey;
              _1687_genKey = ((_1678_generatedValues).Select(_1679_i)).dtor__0;
              RAST._IExpr _1688_genValue;
              _1688_genValue = ((_1678_generatedValues).Select(_1679_i)).dtor__1;
              _1686_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1686_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1687_genKey, _1688_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _1679_i = (_1679_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_1686_arguments);
            RAST._IExpr _out377;
            DCOMP._IOwnership _out378;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out377, out _out378);
            r = _out377;
            resultingOwnership = _out378;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SeqUpdate) {
          DAST._IExpression _1689_expr = _source74.dtor_expr;
          DAST._IExpression _1690_index = _source74.dtor_indexExpr;
          DAST._IExpression _1691_value = _source74.dtor_value;
          unmatched74 = false;
          {
            RAST._IExpr _1692_exprR;
            DCOMP._IOwnership _1693___v123;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1694_exprIdents;
            RAST._IExpr _out379;
            DCOMP._IOwnership _out380;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out381;
            (this).GenExpr(_1689_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out379, out _out380, out _out381);
            _1692_exprR = _out379;
            _1693___v123 = _out380;
            _1694_exprIdents = _out381;
            RAST._IExpr _1695_indexR;
            DCOMP._IOwnership _1696_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1697_indexIdents;
            RAST._IExpr _out382;
            DCOMP._IOwnership _out383;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out384;
            (this).GenExpr(_1690_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out382, out _out383, out _out384);
            _1695_indexR = _out382;
            _1696_indexOwnership = _out383;
            _1697_indexIdents = _out384;
            RAST._IExpr _1698_valueR;
            DCOMP._IOwnership _1699_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1700_valueIdents;
            RAST._IExpr _out385;
            DCOMP._IOwnership _out386;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out387;
            (this).GenExpr(_1691_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out385, out _out386, out _out387);
            _1698_valueR = _out385;
            _1699_valueOwnership = _out386;
            _1700_valueIdents = _out387;
            r = ((_1692_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1695_indexR, _1698_valueR));
            RAST._IExpr _out388;
            DCOMP._IOwnership _out389;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out388, out _out389);
            r = _out388;
            resultingOwnership = _out389;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1694_exprIdents, _1697_indexIdents), _1700_valueIdents);
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MapUpdate) {
          DAST._IExpression _1701_expr = _source74.dtor_expr;
          DAST._IExpression _1702_index = _source74.dtor_indexExpr;
          DAST._IExpression _1703_value = _source74.dtor_value;
          unmatched74 = false;
          {
            RAST._IExpr _1704_exprR;
            DCOMP._IOwnership _1705___v124;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1706_exprIdents;
            RAST._IExpr _out390;
            DCOMP._IOwnership _out391;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out392;
            (this).GenExpr(_1701_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out390, out _out391, out _out392);
            _1704_exprR = _out390;
            _1705___v124 = _out391;
            _1706_exprIdents = _out392;
            RAST._IExpr _1707_indexR;
            DCOMP._IOwnership _1708_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1709_indexIdents;
            RAST._IExpr _out393;
            DCOMP._IOwnership _out394;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out395;
            (this).GenExpr(_1702_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out393, out _out394, out _out395);
            _1707_indexR = _out393;
            _1708_indexOwnership = _out394;
            _1709_indexIdents = _out395;
            RAST._IExpr _1710_valueR;
            DCOMP._IOwnership _1711_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1712_valueIdents;
            RAST._IExpr _out396;
            DCOMP._IOwnership _out397;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out398;
            (this).GenExpr(_1703_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out396, out _out397, out _out398);
            _1710_valueR = _out396;
            _1711_valueOwnership = _out397;
            _1712_valueIdents = _out398;
            r = ((_1704_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1707_indexR, _1710_valueR));
            RAST._IExpr _out399;
            DCOMP._IOwnership _out400;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out399, out _out400);
            r = _out399;
            resultingOwnership = _out400;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1706_exprIdents, _1709_indexIdents), _1712_valueIdents);
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_This) {
          unmatched74 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source75 = selfIdent;
            bool unmatched75 = true;
            if (unmatched75) {
              if (_source75.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1713_id = _source75.dtor_value;
                unmatched75 = false;
                {
                  r = RAST.Expr.create_Identifier(_1713_id);
                  if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
                    r = RAST.__default.Clone(r);
                    resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
                  } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
                    r = RAST.__default.BoxNew(RAST.__default.Clone(r));
                    resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
                  } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
                    if (!(_1713_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                      r = RAST.__default.Borrow(r);
                    }
                    resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
                  } else {
                    if (!(_1713_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                      r = RAST.__default.BorrowMut(r);
                    }
                    resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
                  }
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1713_id);
                }
              }
            }
            if (unmatched75) {
              unmatched75 = false;
              {
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")"));
                RAST._IExpr _out401;
                DCOMP._IOwnership _out402;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out401, out _out402);
                r = _out401;
                resultingOwnership = _out402;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              }
            }
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Ite) {
          DAST._IExpression _1714_cond = _source74.dtor_cond;
          DAST._IExpression _1715_t = _source74.dtor_thn;
          DAST._IExpression _1716_f = _source74.dtor_els;
          unmatched74 = false;
          {
            RAST._IExpr _1717_cond;
            DCOMP._IOwnership _1718___v125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1719_recIdentsCond;
            RAST._IExpr _out403;
            DCOMP._IOwnership _out404;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out405;
            (this).GenExpr(_1714_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out403, out _out404, out _out405);
            _1717_cond = _out403;
            _1718___v125 = _out404;
            _1719_recIdentsCond = _out405;
            Dafny.ISequence<Dafny.Rune> _1720_condString;
            _1720_condString = (_1717_cond)._ToString(DCOMP.__default.IND);
            RAST._IExpr _1721___v126;
            DCOMP._IOwnership _1722_tHasToBeOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1723___v127;
            RAST._IExpr _out406;
            DCOMP._IOwnership _out407;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out408;
            (this).GenExpr(_1715_t, selfIdent, env, expectedOwnership, out _out406, out _out407, out _out408);
            _1721___v126 = _out406;
            _1722_tHasToBeOwned = _out407;
            _1723___v127 = _out408;
            RAST._IExpr _1724_fExpr;
            DCOMP._IOwnership _1725_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1726_recIdentsF;
            RAST._IExpr _out409;
            DCOMP._IOwnership _out410;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out411;
            (this).GenExpr(_1716_f, selfIdent, env, _1722_tHasToBeOwned, out _out409, out _out410, out _out411);
            _1724_fExpr = _out409;
            _1725_fOwned = _out410;
            _1726_recIdentsF = _out411;
            Dafny.ISequence<Dafny.Rune> _1727_fString;
            _1727_fString = (_1724_fExpr)._ToString(DCOMP.__default.IND);
            RAST._IExpr _1728_tExpr;
            DCOMP._IOwnership _1729___v128;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1730_recIdentsT;
            RAST._IExpr _out412;
            DCOMP._IOwnership _out413;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out414;
            (this).GenExpr(_1715_t, selfIdent, env, _1725_fOwned, out _out412, out _out413, out _out414);
            _1728_tExpr = _out412;
            _1729___v128 = _out413;
            _1730_recIdentsT = _out414;
            Dafny.ISequence<Dafny.Rune> _1731_tString;
            _1731_tString = (_1728_tExpr)._ToString(DCOMP.__default.IND);
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _1720_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _1731_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _1727_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})")));
            RAST._IExpr _out415;
            DCOMP._IOwnership _out416;
            DCOMP.COMP.FromOwnership(r, _1725_fOwned, expectedOwnership, out _out415, out _out416);
            r = _out415;
            resultingOwnership = _out416;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1719_recIdentsCond, _1730_recIdentsT), _1726_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source74.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _1732_e = _source74.dtor_expr;
            DAST.Format._IUnaryOpFormat _1733_format = _source74.dtor_format1;
            unmatched74 = false;
            {
              RAST._IExpr _1734_recursiveGen;
              DCOMP._IOwnership _1735___v129;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1736_recIdents;
              RAST._IExpr _out417;
              DCOMP._IOwnership _out418;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out419;
              (this).GenExpr(_1732_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out417, out _out418, out _out419);
              _1734_recursiveGen = _out417;
              _1735___v129 = _out418;
              _1736_recIdents = _out419;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _1734_recursiveGen, _1733_format);
              RAST._IExpr _out420;
              DCOMP._IOwnership _out421;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out420, out _out421);
              r = _out420;
              resultingOwnership = _out421;
              readIdents = _1736_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source74.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _1737_e = _source74.dtor_expr;
            DAST.Format._IUnaryOpFormat _1738_format = _source74.dtor_format1;
            unmatched74 = false;
            {
              RAST._IExpr _1739_recursiveGen;
              DCOMP._IOwnership _1740___v130;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1741_recIdents;
              RAST._IExpr _out422;
              DCOMP._IOwnership _out423;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out424;
              (this).GenExpr(_1737_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out422, out _out423, out _out424);
              _1739_recursiveGen = _out422;
              _1740___v130 = _out423;
              _1741_recIdents = _out424;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _1739_recursiveGen, _1738_format);
              RAST._IExpr _out425;
              DCOMP._IOwnership _out426;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out425, out _out426);
              r = _out425;
              resultingOwnership = _out426;
              readIdents = _1741_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source74.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _1742_e = _source74.dtor_expr;
            DAST.Format._IUnaryOpFormat _1743_format = _source74.dtor_format1;
            unmatched74 = false;
            {
              RAST._IExpr _1744_recursiveGen;
              DCOMP._IOwnership _1745_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1746_recIdents;
              RAST._IExpr _out427;
              DCOMP._IOwnership _out428;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out429;
              (this).GenExpr(_1742_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out427, out _out428, out _out429);
              _1744_recursiveGen = _out427;
              _1745_recOwned = _out428;
              _1746_recIdents = _out429;
              r = ((_1744_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out430;
              DCOMP._IOwnership _out431;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out430, out _out431);
              r = _out430;
              resultingOwnership = _out431;
              readIdents = _1746_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_BinOp) {
          DAST._IBinOp _1747___v131 = _source74.dtor_op;
          DAST._IExpression _1748___v132 = _source74.dtor_left;
          DAST._IExpression _1749___v133 = _source74.dtor_right;
          DAST.Format._IBinaryOpFormat _1750___v134 = _source74.dtor_format2;
          unmatched74 = false;
          RAST._IExpr _out432;
          DCOMP._IOwnership _out433;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out434;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out432, out _out433, out _out434);
          r = _out432;
          resultingOwnership = _out433;
          readIdents = _out434;
        }
      }
      if (unmatched74) {
        if (_source74.is_ArrayLen) {
          DAST._IExpression _1751_expr = _source74.dtor_expr;
          BigInteger _1752_dim = _source74.dtor_dim;
          unmatched74 = false;
          {
            RAST._IExpr _1753_recursiveGen;
            DCOMP._IOwnership _1754___v135;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1755_recIdents;
            RAST._IExpr _out435;
            DCOMP._IOwnership _out436;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out437;
            (this).GenExpr(_1751_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out435, out _out436, out _out437);
            _1753_recursiveGen = _out435;
            _1754___v135 = _out436;
            _1755_recIdents = _out437;
            if ((_1752_dim).Sign == 0) {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), (_1753_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())")));
            } else {
              Dafny.ISequence<Dafny.Rune> _1756_s;
              _1756_s = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(m.borrow().len())")))._ToString(DCOMP.__default.IND);
              BigInteger _1757_i;
              _1757_i = BigInteger.One;
              while ((_1757_i) < (_1752_dim)) {
                _1756_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("m.borrow().get(0).map(|m| "), _1756_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"));
                _1757_i = (_1757_i) + (BigInteger.One);
              }
              r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_1753_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow().get(0).map(|m| ")), _1756_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"))));
            }
            RAST._IExpr _out438;
            DCOMP._IOwnership _out439;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out438, out _out439);
            r = _out438;
            resultingOwnership = _out439;
            readIdents = _1755_recIdents;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MapKeys) {
          DAST._IExpression _1758_expr = _source74.dtor_expr;
          unmatched74 = false;
          {
            RAST._IExpr _1759_recursiveGen;
            DCOMP._IOwnership _1760___v136;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1761_recIdents;
            RAST._IExpr _out440;
            DCOMP._IOwnership _out441;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out442;
            (this).GenExpr(_1758_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out440, out _out441, out _out442);
            _1759_recursiveGen = _out440;
            _1760___v136 = _out441;
            _1761_recIdents = _out442;
            readIdents = _1761_recIdents;
            r = ((_1759_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out443;
            DCOMP._IOwnership _out444;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out443, out _out444);
            r = _out443;
            resultingOwnership = _out444;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MapValues) {
          DAST._IExpression _1762_expr = _source74.dtor_expr;
          unmatched74 = false;
          {
            RAST._IExpr _1763_recursiveGen;
            DCOMP._IOwnership _1764___v137;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1765_recIdents;
            RAST._IExpr _out445;
            DCOMP._IOwnership _out446;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out447;
            (this).GenExpr(_1762_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out445, out _out446, out _out447);
            _1763_recursiveGen = _out445;
            _1764___v137 = _out446;
            _1765_recIdents = _out447;
            readIdents = _1765_recIdents;
            r = ((_1763_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out448;
            DCOMP._IOwnership _out449;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out448, out _out449);
            r = _out448;
            resultingOwnership = _out449;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SelectFn) {
          DAST._IExpression _1766_on = _source74.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1767_field = _source74.dtor_field;
          bool _1768_isDatatype = _source74.dtor_onDatatype;
          bool _1769_isStatic = _source74.dtor_isStatic;
          BigInteger _1770_arity = _source74.dtor_arity;
          unmatched74 = false;
          {
            RAST._IExpr _1771_onExpr;
            DCOMP._IOwnership _1772_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1773_recIdents;
            RAST._IExpr _out450;
            DCOMP._IOwnership _out451;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out452;
            (this).GenExpr(_1766_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out450, out _out451, out _out452);
            _1771_onExpr = _out450;
            _1772_onOwned = _out451;
            _1773_recIdents = _out452;
            Dafny.ISequence<Dafny.Rune> _1774_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _1775_onString;
            _1775_onString = (_1771_onExpr)._ToString(DCOMP.__default.IND);
            if (_1769_isStatic) {
              _1774_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1775_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_1767_field));
            } else {
              _1774_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _1774_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1774_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _1775_onString), ((object.Equals(_1772_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _1776_args;
              _1776_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _1777_i;
              _1777_i = BigInteger.Zero;
              while ((_1777_i) < (_1770_arity)) {
                if ((_1777_i).Sign == 1) {
                  _1776_args = Dafny.Sequence<Dafny.Rune>.Concat(_1776_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _1776_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1776_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_1777_i));
                _1777_i = (_1777_i) + (BigInteger.One);
              }
              _1774_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1774_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _1776_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _1774_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1774_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_1767_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1776_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _1774_s = Dafny.Sequence<Dafny.Rune>.Concat(_1774_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _1774_s = Dafny.Sequence<Dafny.Rune>.Concat(_1774_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _1778_typeShape;
            _1778_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _1779_i;
            _1779_i = BigInteger.Zero;
            while ((_1779_i) < (_1770_arity)) {
              if ((_1779_i).Sign == 1) {
                _1778_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1778_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _1778_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1778_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _1779_i = (_1779_i) + (BigInteger.One);
            }
            _1778_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1778_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _1774_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _1774_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _1778_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_1774_s);
            RAST._IExpr _out453;
            DCOMP._IOwnership _out454;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out453, out _out454);
            r = _out453;
            resultingOwnership = _out454;
            readIdents = _1773_recIdents;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Select) {
          DAST._IExpression expr0 = _source74.dtor_expr;
          if (expr0.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1780_c = expr0.dtor_Companion_a0;
            Dafny.ISequence<Dafny.Rune> _1781_field = _source74.dtor_field;
            bool _1782_isConstant = _source74.dtor_isConstant;
            bool _1783_isDatatype = _source74.dtor_onDatatype;
            DAST._IType _1784_fieldType = _source74.dtor_fieldType;
            unmatched74 = false;
            {
              RAST._IExpr _1785_onExpr;
              DCOMP._IOwnership _1786_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1787_recIdents;
              RAST._IExpr _out455;
              DCOMP._IOwnership _out456;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out457;
              (this).GenExpr(DAST.Expression.create_Companion(_1780_c), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out455, out _out456, out _out457);
              _1785_onExpr = _out455;
              _1786_onOwned = _out456;
              _1787_recIdents = _out457;
              r = ((_1785_onExpr).MSel(DCOMP.__default.escapeName(_1781_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out458;
              DCOMP._IOwnership _out459;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out458, out _out459);
              r = _out458;
              resultingOwnership = _out459;
              readIdents = _1787_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Select) {
          DAST._IExpression _1788_on = _source74.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1789_field = _source74.dtor_field;
          bool _1790_isConstant = _source74.dtor_isConstant;
          bool _1791_isDatatype = _source74.dtor_onDatatype;
          DAST._IType _1792_fieldType = _source74.dtor_fieldType;
          unmatched74 = false;
          {
            if (_1791_isDatatype) {
              RAST._IExpr _1793_onExpr;
              DCOMP._IOwnership _1794_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1795_recIdents;
              RAST._IExpr _out460;
              DCOMP._IOwnership _out461;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out462;
              (this).GenExpr(_1788_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out460, out _out461, out _out462);
              _1793_onExpr = _out460;
              _1794_onOwned = _out461;
              _1795_recIdents = _out462;
              r = ((_1793_onExpr).Sel(DCOMP.__default.escapeName(_1789_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _1796_typ;
              RAST._IType _out463;
              _out463 = (this).GenType(_1792_fieldType, false, false);
              _1796_typ = _out463;
              RAST._IExpr _out464;
              DCOMP._IOwnership _out465;
              DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out464, out _out465);
              r = _out464;
              resultingOwnership = _out465;
              readIdents = _1795_recIdents;
            } else {
              RAST._IExpr _1797_onExpr;
              DCOMP._IOwnership _1798_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1799_recIdents;
              RAST._IExpr _out466;
              DCOMP._IOwnership _out467;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out468;
              (this).GenExpr(_1788_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out466, out _out467, out _out468);
              _1797_onExpr = _out466;
              _1798_onOwned = _out467;
              _1799_recIdents = _out468;
              r = _1797_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_1789_field));
              if (_1790_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _1800_s;
                _1800_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_1797_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_1789_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_1800_s);
              }
              DCOMP._IOwnership _1801_fromOwnership;
              _1801_fromOwnership = ((_1790_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out469;
              DCOMP._IOwnership _out470;
              DCOMP.COMP.FromOwnership(r, _1801_fromOwnership, expectedOwnership, out _out469, out _out470);
              r = _out469;
              resultingOwnership = _out470;
              readIdents = _1799_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Index) {
          DAST._IExpression _1802_on = _source74.dtor_expr;
          DAST._ICollKind _1803_collKind = _source74.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _1804_indices = _source74.dtor_indices;
          unmatched74 = false;
          {
            RAST._IExpr _1805_onExpr;
            DCOMP._IOwnership _1806_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1807_recIdents;
            RAST._IExpr _out471;
            DCOMP._IOwnership _out472;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out473;
            (this).GenExpr(_1802_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out471, out _out472, out _out473);
            _1805_onExpr = _out471;
            _1806_onOwned = _out472;
            _1807_recIdents = _out473;
            readIdents = _1807_recIdents;
            r = _1805_onExpr;
            BigInteger _1808_i;
            _1808_i = BigInteger.Zero;
            while ((_1808_i) < (new BigInteger((_1804_indices).Count))) {
              if (object.Equals(_1803_collKind, DAST.CollKind.create_Array())) {
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              RAST._IExpr _1809_idx;
              DCOMP._IOwnership _1810_idxOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1811_recIdentsIdx;
              RAST._IExpr _out474;
              DCOMP._IOwnership _out475;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out476;
              (this).GenExpr((_1804_indices).Select(_1808_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out474, out _out475, out _out476);
              _1809_idx = _out474;
              _1810_idxOwned = _out475;
              _1811_recIdentsIdx = _out476;
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_1809_idx);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1811_recIdentsIdx);
              _1808_i = (_1808_i) + (BigInteger.One);
            }
            RAST._IExpr _out477;
            DCOMP._IOwnership _out478;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out477, out _out478);
            r = _out477;
            resultingOwnership = _out478;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_IndexRange) {
          DAST._IExpression _1812_on = _source74.dtor_expr;
          bool _1813_isArray = _source74.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _1814_low = _source74.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _1815_high = _source74.dtor_high;
          unmatched74 = false;
          {
            RAST._IExpr _1816_onExpr;
            DCOMP._IOwnership _1817_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1818_recIdents;
            RAST._IExpr _out479;
            DCOMP._IOwnership _out480;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out481;
            (this).GenExpr(_1812_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out479, out _out480, out _out481);
            _1816_onExpr = _out479;
            _1817_onOwned = _out480;
            _1818_recIdents = _out481;
            readIdents = _1818_recIdents;
            Dafny.ISequence<Dafny.Rune> _1819_methodName;
            _1819_methodName = (((_1814_low).is_Some) ? ((((_1815_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_1815_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _1820_arguments;
            _1820_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source76 = _1814_low;
            bool unmatched76 = true;
            if (unmatched76) {
              if (_source76.is_Some) {
                DAST._IExpression _1821_l = _source76.dtor_value;
                unmatched76 = false;
                {
                  RAST._IExpr _1822_lExpr;
                  DCOMP._IOwnership _1823___v138;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1824_recIdentsL;
                  RAST._IExpr _out482;
                  DCOMP._IOwnership _out483;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out484;
                  (this).GenExpr(_1821_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out482, out _out483, out _out484);
                  _1822_lExpr = _out482;
                  _1823___v138 = _out483;
                  _1824_recIdentsL = _out484;
                  _1820_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1820_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1822_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1824_recIdentsL);
                }
              }
            }
            if (unmatched76) {
              unmatched76 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source77 = _1815_high;
            bool unmatched77 = true;
            if (unmatched77) {
              if (_source77.is_Some) {
                DAST._IExpression _1825_h = _source77.dtor_value;
                unmatched77 = false;
                {
                  RAST._IExpr _1826_hExpr;
                  DCOMP._IOwnership _1827___v139;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1828_recIdentsH;
                  RAST._IExpr _out485;
                  DCOMP._IOwnership _out486;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out487;
                  (this).GenExpr(_1825_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out485, out _out486, out _out487);
                  _1826_hExpr = _out485;
                  _1827___v139 = _out486;
                  _1828_recIdentsH = _out487;
                  _1820_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1820_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1826_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1828_recIdentsH);
                }
              }
            }
            if (unmatched77) {
              unmatched77 = false;
            }
            r = _1816_onExpr;
            if (_1813_isArray) {
              if (!(_1819_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _1819_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1819_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _1819_methodName))).Apply(_1820_arguments);
            } else {
              if (!(_1819_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_1819_methodName)).Apply(_1820_arguments);
              }
            }
            RAST._IExpr _out488;
            DCOMP._IOwnership _out489;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out488, out _out489);
            r = _out488;
            resultingOwnership = _out489;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_TupleSelect) {
          DAST._IExpression _1829_on = _source74.dtor_expr;
          BigInteger _1830_idx = _source74.dtor_index;
          DAST._IType _1831_fieldType = _source74.dtor_fieldType;
          unmatched74 = false;
          {
            RAST._IExpr _1832_onExpr;
            DCOMP._IOwnership _1833_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1834_recIdents;
            RAST._IExpr _out490;
            DCOMP._IOwnership _out491;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out492;
            (this).GenExpr(_1829_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out490, out _out491, out _out492);
            _1832_onExpr = _out490;
            _1833_onOwnership = _out491;
            _1834_recIdents = _out492;
            Dafny.ISequence<Dafny.Rune> _1835_selName;
            _1835_selName = Std.Strings.__default.OfNat(_1830_idx);
            DAST._IType _source78 = _1831_fieldType;
            bool unmatched78 = true;
            if (unmatched78) {
              if (_source78.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1836_tps = _source78.dtor_Tuple_a0;
                unmatched78 = false;
                if (((_1831_fieldType).is_Tuple) && ((new BigInteger((_1836_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _1835_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1835_selName);
                }
              }
            }
            if (unmatched78) {
              DAST._IType _1837___v140 = _source78;
              unmatched78 = false;
            }
            r = (_1832_onExpr).Sel(_1835_selName);
            RAST._IExpr _out493;
            DCOMP._IOwnership _out494;
            DCOMP.COMP.FromOwnership(r, _1833_onOwnership, expectedOwnership, out _out493, out _out494);
            r = _out493;
            resultingOwnership = _out494;
            readIdents = _1834_recIdents;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Call) {
          DAST._IExpression _1838_on = _source74.dtor_on;
          DAST._ICallName _1839_name = _source74.dtor_callName;
          Dafny.ISequence<DAST._IType> _1840_typeArgs = _source74.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1841_args = _source74.dtor_args;
          unmatched74 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IExpr _1842_onExpr;
            DCOMP._IOwnership _1843___v141;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1844_recIdents;
            RAST._IExpr _out495;
            DCOMP._IOwnership _out496;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out497;
            (this).GenExpr(_1838_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out495, out _out496, out _out497);
            _1842_onExpr = _out495;
            _1843___v141 = _out496;
            _1844_recIdents = _out497;
            Dafny.ISequence<RAST._IType> _1845_typeExprs;
            _1845_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
            if ((new BigInteger((_1840_typeArgs).Count)) >= (BigInteger.One)) {
              BigInteger _hi35 = new BigInteger((_1840_typeArgs).Count);
              for (BigInteger _1846_typeI = BigInteger.Zero; _1846_typeI < _hi35; _1846_typeI++) {
                RAST._IType _1847_typeExpr;
                RAST._IType _out498;
                _out498 = (this).GenType((_1840_typeArgs).Select(_1846_typeI), false, false);
                _1847_typeExpr = _out498;
                _1845_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1845_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1847_typeExpr));
              }
            }
            Dafny.ISequence<RAST._IExpr> _1848_argExprs;
            _1848_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi36 = new BigInteger((_1841_args).Count);
            for (BigInteger _1849_i = BigInteger.Zero; _1849_i < _hi36; _1849_i++) {
              DCOMP._IOwnership _1850_argOwnership;
              _1850_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              if (((_1839_name).is_CallName) && ((_1849_i) < (new BigInteger((((_1839_name).dtor_signature)).Count)))) {
                RAST._IType _1851_tpe;
                RAST._IType _out499;
                _out499 = (this).GenType(((((_1839_name).dtor_signature)).Select(_1849_i)).dtor_typ, false, false);
                _1851_tpe = _out499;
                if ((_1851_tpe).CanReadWithoutClone()) {
                  _1850_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
                }
              }
              RAST._IExpr _1852_argExpr;
              DCOMP._IOwnership _1853___v142;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1854_argIdents;
              RAST._IExpr _out500;
              DCOMP._IOwnership _out501;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out502;
              (this).GenExpr((_1841_args).Select(_1849_i), selfIdent, env, _1850_argOwnership, out _out500, out _out501, out _out502);
              _1852_argExpr = _out500;
              _1853___v142 = _out501;
              _1854_argIdents = _out502;
              _1848_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1848_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1852_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1854_argIdents);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1844_recIdents);
            Dafny.ISequence<Dafny.Rune> _1855_renderedName;
            _1855_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
              DAST._ICallName _source79 = _1839_name;
              bool unmatched79 = true;
              if (unmatched79) {
                if (_source79.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _1856_ident = _source79.dtor_name;
                  Std.Wrappers._IOption<DAST._IType> _1857___v143 = _source79.dtor_onType;
                  Dafny.ISequence<DAST._IFormal> _1858___v144 = _source79.dtor_signature;
                  unmatched79 = false;
                  return DCOMP.__default.escapeName(_1856_ident);
                }
              }
              if (unmatched79) {
                bool disjunctiveMatch12 = false;
                if (_source79.is_MapBuilderAdd) {
                  disjunctiveMatch12 = true;
                }
                if (_source79.is_SetBuilderAdd) {
                  disjunctiveMatch12 = true;
                }
                if (disjunctiveMatch12) {
                  unmatched79 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                }
              }
              if (unmatched79) {
                bool disjunctiveMatch13 = false;
                disjunctiveMatch13 = true;
                disjunctiveMatch13 = true;
                if (disjunctiveMatch13) {
                  unmatched79 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                }
              }
              throw new System.Exception("unexpected control point");
            }))();
            DAST._IExpression _source80 = _1838_on;
            bool unmatched80 = true;
            if (unmatched80) {
              if (_source80.is_Companion) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1859___v145 = _source80.dtor_Companion_a0;
                unmatched80 = false;
                {
                  _1842_onExpr = (_1842_onExpr).MSel(_1855_renderedName);
                }
              }
            }
            if (unmatched80) {
              DAST._IExpression _1860___v146 = _source80;
              unmatched80 = false;
              {
                _1842_onExpr = (_1842_onExpr).Sel(_1855_renderedName);
              }
            }
            r = _1842_onExpr;
            if ((new BigInteger((_1845_typeExprs).Count)).Sign == 1) {
              r = (r).ApplyType(_1845_typeExprs);
            }
            r = (r).Apply(_1848_argExprs);
            RAST._IExpr _out503;
            DCOMP._IOwnership _out504;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out503, out _out504);
            r = _out503;
            resultingOwnership = _out504;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _1861_paramsDafny = _source74.dtor_params;
          DAST._IType _1862_retType = _source74.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _1863_body = _source74.dtor_body;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IFormal> _1864_params;
            Dafny.ISequence<RAST._IFormal> _out505;
            _out505 = (this).GenParams(_1861_paramsDafny);
            _1864_params = _out505;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1865_paramNames;
            _1865_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1866_paramTypesMap;
            _1866_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi37 = new BigInteger((_1864_params).Count);
            for (BigInteger _1867_i = BigInteger.Zero; _1867_i < _hi37; _1867_i++) {
              Dafny.ISequence<Dafny.Rune> _1868_name;
              _1868_name = ((_1864_params).Select(_1867_i)).dtor_name;
              _1865_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1865_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1868_name));
              _1866_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1866_paramTypesMap, _1868_name, ((_1864_params).Select(_1867_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _1869_env;
            _1869_env = DCOMP.Environment.create(_1865_paramNames, _1866_paramTypesMap);
            RAST._IExpr _1870_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1871_recIdents;
            DCOMP._IEnvironment _1872___v147;
            RAST._IExpr _out506;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out507;
            DCOMP._IEnvironment _out508;
            (this).GenStmts(_1863_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), _1869_env, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out506, out _out507, out _out508);
            _1870_recursiveGen = _out506;
            _1871_recIdents = _out507;
            _1872___v147 = _out508;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _1871_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1871_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_1873_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll6 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in (_1873_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _1874_name = (Dafny.ISequence<Dafny.Rune>)_compr_6;
                if ((_1873_paramNames).Contains(_1874_name)) {
                  _coll6.Add(_1874_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll6);
            }))())(_1865_paramNames));
            RAST._IExpr _1875_allReadCloned;
            _1875_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_1871_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _1876_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_1871_recIdents).Elements) {
                _1876_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_1871_recIdents).Contains(_1876_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 3734)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) && ((_1876_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
                  _1875_allReadCloned = (_1875_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
                }
              } else if (!((_1865_paramNames).Contains(_1876_next))) {
                _1875_allReadCloned = (_1875_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1876_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.Expr.create_Identifier(_1876_next)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1876_next));
              }
              _1871_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1871_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1876_next));
            }
            RAST._IType _1877_retTypeGen;
            RAST._IType _out509;
            _out509 = (this).GenType(_1862_retType, false, true);
            _1877_retTypeGen = _out509;
            r = RAST.Expr.create_Block((_1875_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_1864_params, Std.Wrappers.Option<RAST._IType>.create_Some(_1877_retTypeGen), RAST.Expr.create_Block(_1870_recursiveGen)))));
            RAST._IExpr _out510;
            DCOMP._IOwnership _out511;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out510, out _out511);
            r = _out510;
            resultingOwnership = _out511;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _1878_values = _source74.dtor_values;
          DAST._IType _1879_retType = _source74.dtor_retType;
          DAST._IExpression _1880_expr = _source74.dtor_expr;
          unmatched74 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1881_paramNames;
            _1881_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _1882_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out512;
            _out512 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_1883_value) => {
              return (_1883_value).dtor__0;
            })), _1878_values));
            _1882_paramFormals = _out512;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1884_paramTypes;
            _1884_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1885_paramNamesSet;
            _1885_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi38 = new BigInteger((_1878_values).Count);
            for (BigInteger _1886_i = BigInteger.Zero; _1886_i < _hi38; _1886_i++) {
              Dafny.ISequence<Dafny.Rune> _1887_name;
              _1887_name = (((_1878_values).Select(_1886_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _1888_rName;
              _1888_rName = DCOMP.__default.escapeName(_1887_name);
              _1881_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1881_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1888_rName));
              _1884_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1884_paramTypes, _1888_rName, ((_1882_paramFormals).Select(_1886_i)).dtor_tpe);
              _1885_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1885_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1888_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi39 = new BigInteger((_1878_values).Count);
            for (BigInteger _1889_i = BigInteger.Zero; _1889_i < _hi39; _1889_i++) {
              RAST._IType _1890_typeGen;
              RAST._IType _out513;
              _out513 = (this).GenType((((_1878_values).Select(_1889_i)).dtor__0).dtor_typ, false, true);
              _1890_typeGen = _out513;
              RAST._IExpr _1891_valueGen;
              DCOMP._IOwnership _1892___v148;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1893_recIdents;
              RAST._IExpr _out514;
              DCOMP._IOwnership _out515;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out516;
              (this).GenExpr(((_1878_values).Select(_1889_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out514, out _out515, out _out516);
              _1891_valueGen = _out514;
              _1892___v148 = _out515;
              _1893_recIdents = _out516;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_1878_values).Select(_1889_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1890_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1891_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1893_recIdents);
            }
            DCOMP._IEnvironment _1894_newEnv;
            _1894_newEnv = DCOMP.Environment.create(_1881_paramNames, _1884_paramTypes);
            RAST._IExpr _1895_recGen;
            DCOMP._IOwnership _1896_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1897_recIdents;
            RAST._IExpr _out517;
            DCOMP._IOwnership _out518;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out519;
            (this).GenExpr(_1880_expr, selfIdent, _1894_newEnv, expectedOwnership, out _out517, out _out518, out _out519);
            _1895_recGen = _out517;
            _1896_recOwned = _out518;
            _1897_recIdents = _out519;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1897_recIdents, _1885_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_1895_recGen));
            RAST._IExpr _out520;
            DCOMP._IOwnership _out521;
            DCOMP.COMP.FromOwnership(r, _1896_recOwned, expectedOwnership, out _out520, out _out521);
            r = _out520;
            resultingOwnership = _out521;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _1898_name = _source74.dtor_name;
          DAST._IType _1899_tpe = _source74.dtor_typ;
          DAST._IExpression _1900_value = _source74.dtor_value;
          DAST._IExpression _1901_iifeBody = _source74.dtor_iifeBody;
          unmatched74 = false;
          {
            RAST._IExpr _1902_valueGen;
            DCOMP._IOwnership _1903___v149;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1904_recIdents;
            RAST._IExpr _out522;
            DCOMP._IOwnership _out523;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out524;
            (this).GenExpr(_1900_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out522, out _out523, out _out524);
            _1902_valueGen = _out522;
            _1903___v149 = _out523;
            _1904_recIdents = _out524;
            readIdents = _1904_recIdents;
            RAST._IType _1905_valueTypeGen;
            RAST._IType _out525;
            _out525 = (this).GenType(_1899_tpe, false, true);
            _1905_valueTypeGen = _out525;
            RAST._IExpr _1906_bodyGen;
            DCOMP._IOwnership _1907___v150;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1908_bodyIdents;
            RAST._IExpr _out526;
            DCOMP._IOwnership _out527;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out528;
            (this).GenExpr(_1901_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out526, out _out527, out _out528);
            _1906_bodyGen = _out526;
            _1907___v150 = _out527;
            _1908_bodyIdents = _out528;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1908_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_1898_name)))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_1898_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_1905_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1902_valueGen))).Then(_1906_bodyGen));
            RAST._IExpr _out529;
            DCOMP._IOwnership _out530;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out529, out _out530);
            r = _out529;
            resultingOwnership = _out530;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Apply) {
          DAST._IExpression _1909_func = _source74.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _1910_args = _source74.dtor_args;
          unmatched74 = false;
          {
            RAST._IExpr _1911_funcExpr;
            DCOMP._IOwnership _1912___v151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1913_recIdents;
            RAST._IExpr _out531;
            DCOMP._IOwnership _out532;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out533;
            (this).GenExpr(_1909_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out531, out _out532, out _out533);
            _1911_funcExpr = _out531;
            _1912___v151 = _out532;
            _1913_recIdents = _out533;
            readIdents = _1913_recIdents;
            Dafny.ISequence<RAST._IExpr> _1914_rArgs;
            _1914_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi40 = new BigInteger((_1910_args).Count);
            for (BigInteger _1915_i = BigInteger.Zero; _1915_i < _hi40; _1915_i++) {
              RAST._IExpr _1916_argExpr;
              DCOMP._IOwnership _1917_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1918_argIdents;
              RAST._IExpr _out534;
              DCOMP._IOwnership _out535;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out536;
              (this).GenExpr((_1910_args).Select(_1915_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out534, out _out535, out _out536);
              _1916_argExpr = _out534;
              _1917_argOwned = _out535;
              _1918_argIdents = _out536;
              _1914_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1914_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1916_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1918_argIdents);
            }
            r = (_1911_funcExpr).Apply(_1914_rArgs);
            RAST._IExpr _out537;
            DCOMP._IOwnership _out538;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out537, out _out538);
            r = _out537;
            resultingOwnership = _out538;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_TypeTest) {
          DAST._IExpression _1919_on = _source74.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1920_dType = _source74.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _1921_variant = _source74.dtor_variant;
          unmatched74 = false;
          {
            RAST._IExpr _1922_exprGen;
            DCOMP._IOwnership _1923___v152;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1924_recIdents;
            RAST._IExpr _out539;
            DCOMP._IOwnership _out540;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
            (this).GenExpr(_1919_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out539, out _out540, out _out541);
            _1922_exprGen = _out539;
            _1923___v152 = _out540;
            _1924_recIdents = _out541;
            RAST._IType _1925_dTypePath;
            RAST._IType _out542;
            _out542 = DCOMP.COMP.GenPath(_1920_dType);
            _1925_dTypePath = _out542;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_1922_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_1925_dTypePath).MSel(DCOMP.__default.escapeName(_1921_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out543;
            DCOMP._IOwnership _out544;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out543, out _out544);
            r = _out543;
            resultingOwnership = _out544;
            readIdents = _1924_recIdents;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_BoolBoundedPool) {
          unmatched74 = false;
          {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
            RAST._IExpr _out545;
            DCOMP._IOwnership _out546;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out545, out _out546);
            r = _out545;
            resultingOwnership = _out546;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SetBoundedPool) {
          DAST._IExpression _1926_of = _source74.dtor_of;
          unmatched74 = false;
          {
            RAST._IExpr _1927_exprGen;
            DCOMP._IOwnership _1928___v153;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1929_recIdents;
            RAST._IExpr _out547;
            DCOMP._IOwnership _out548;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out549;
            (this).GenExpr(_1926_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out547, out _out548, out _out549);
            _1927_exprGen = _out547;
            _1928___v153 = _out548;
            _1929_recIdents = _out549;
            r = ((((_1927_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out550;
            DCOMP._IOwnership _out551;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out550, out _out551);
            r = _out550;
            resultingOwnership = _out551;
            readIdents = _1929_recIdents;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SeqBoundedPool) {
          DAST._IExpression _1930_of = _source74.dtor_of;
          bool _1931_includeDuplicates = _source74.dtor_includeDuplicates;
          unmatched74 = false;
          {
            RAST._IExpr _1932_exprGen;
            DCOMP._IOwnership _1933___v154;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1934_recIdents;
            RAST._IExpr _out552;
            DCOMP._IOwnership _out553;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out554;
            (this).GenExpr(_1930_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out552, out _out553, out _out554);
            _1932_exprGen = _out552;
            _1933___v154 = _out553;
            _1934_recIdents = _out554;
            r = ((_1932_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_1931_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out555;
            DCOMP._IOwnership _out556;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out555, out _out556);
            r = _out555;
            resultingOwnership = _out556;
            readIdents = _1934_recIdents;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_IntRange) {
          DAST._IExpression _1935_lo = _source74.dtor_lo;
          DAST._IExpression _1936_hi = _source74.dtor_hi;
          unmatched74 = false;
          {
            RAST._IExpr _1937_lo;
            DCOMP._IOwnership _1938___v155;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1939_recIdentsLo;
            RAST._IExpr _out557;
            DCOMP._IOwnership _out558;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out559;
            (this).GenExpr(_1935_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out557, out _out558, out _out559);
            _1937_lo = _out557;
            _1938___v155 = _out558;
            _1939_recIdentsLo = _out559;
            RAST._IExpr _1940_hi;
            DCOMP._IOwnership _1941___v156;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1942_recIdentsHi;
            RAST._IExpr _out560;
            DCOMP._IOwnership _out561;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out562;
            (this).GenExpr(_1936_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out560, out _out561, out _out562);
            _1940_hi = _out560;
            _1941___v156 = _out561;
            _1942_recIdentsHi = _out562;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1937_lo, _1940_hi));
            RAST._IExpr _out563;
            DCOMP._IOwnership _out564;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out563, out _out564);
            r = _out563;
            resultingOwnership = _out564;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1939_recIdentsLo, _1942_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MapBuilder) {
          DAST._IType _1943_keyType = _source74.dtor_keyType;
          DAST._IType _1944_valueType = _source74.dtor_valueType;
          unmatched74 = false;
          {
            RAST._IType _1945_kType;
            RAST._IType _out565;
            _out565 = (this).GenType(_1943_keyType, false, false);
            _1945_kType = _out565;
            RAST._IType _1946_vType;
            RAST._IType _out566;
            _out566 = (this).GenType(_1944_valueType, false, false);
            _1946_vType = _out566;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1945_kType, _1946_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
      if (unmatched74) {
        DAST._IType _1947_elemType = _source74.dtor_elemType;
        unmatched74 = false;
        {
          RAST._IType _1948_eType;
          RAST._IType _out569;
          _out569 = (this).GenType(_1947_elemType, false, false);
          _1948_eType = _out569;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1948_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out570;
          DCOMP._IOwnership _out571;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out570, out _out571);
          r = _out570;
          resultingOwnership = _out571;
          return ;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      BigInteger _1949_i;
      _1949_i = BigInteger.Zero;
      while ((_1949_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _1950_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _1951_m;
        RAST._IMod _out572;
        _out572 = (this).GenModule((p).Select(_1949_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _1951_m = _out572;
        _1950_generated = (_1951_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_1949_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _1950_generated);
        _1949_i = (_1949_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _1952_i;
      _1952_i = BigInteger.Zero;
      while ((_1952_i) < (new BigInteger((fullName).Count))) {
        if ((_1952_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_1952_i)));
        _1952_i = (_1952_i) + (BigInteger.One);
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