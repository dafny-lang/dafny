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
      Dafny.ISequence<Dafny.Rune> _1005___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1005___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1005___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1005___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in123 = (i).Drop(new BigInteger(2));
        i = _in123;
        goto TAIL_CALL_START;
      } else {
        _1005___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1005___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in124 = (i).Drop(BigInteger.One);
        i = _in124;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1006___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1006___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1006___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1006___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in125 = (i).Drop(BigInteger.One);
        i = _in125;
        goto TAIL_CALL_START;
      } else {
        _1006___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1006___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _1007_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1007_r);
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
      BigInteger _1008_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1008_indexInEnv), ((this).dtor_names).Drop((_1008_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
      Dafny.ISequence<Dafny.Rune> _1009_modName;
      _1009_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_1009_modName);
      } else {
        Dafny.ISequence<RAST._IModDecl> _1010_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _1010_body = _out15;
        s = RAST.Mod.create_Mod(_1009_modName, _1010_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi5 = new BigInteger((body).Count);
      for (BigInteger _1011_i = BigInteger.Zero; _1011_i < _hi5; _1011_i++) {
        Dafny.ISequence<RAST._IModDecl> _1012_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source44 = (body).Select(_1011_i);
        if (_source44.is_Module) {
          DAST._IModule _1013_m = _source44.dtor_Module_a0;
          RAST._IMod _1014_mm;
          RAST._IMod _out16;
          _out16 = (this).GenModule(_1013_m, containingPath);
          _1014_mm = _out16;
          _1012_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1014_mm));
          goto after_match1;
        }
        if (_source44.is_Class) {
          DAST._IClass _1015_c = _source44.dtor_Class_a0;
          Dafny.ISequence<RAST._IModDecl> _out17;
          _out17 = (this).GenClass(_1015_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1015_c).dtor_name)));
          _1012_generated = _out17;
          goto after_match1;
        }
        if (_source44.is_Trait) {
          DAST._ITrait _1016_t = _source44.dtor_Trait_a0;
          Dafny.ISequence<Dafny.Rune> _1017_tt;
          Dafny.ISequence<Dafny.Rune> _out18;
          _out18 = (this).GenTrait(_1016_t, containingPath);
          _1017_tt = _out18;
          _1012_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_RawDecl(_1017_tt));
          goto after_match1;
        }
        if (_source44.is_Newtype) {
          DAST._INewtype _1018_n = _source44.dtor_Newtype_a0;
          Dafny.ISequence<RAST._IModDecl> _out19;
          _out19 = (this).GenNewtype(_1018_n);
          _1012_generated = _out19;
          goto after_match1;
        }
        DAST._IDatatype _1019_d = _source44.dtor_Datatype_a0;
        Dafny.ISequence<RAST._IModDecl> _out20;
        _out20 = (this).GenDatatype(_1019_d);
        _1012_generated = _out20;
      after_match1: ;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1012_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1020_genTpConstraint;
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) {
        _1020_genTpConstraint = Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq);
      } else {
        _1020_genTpConstraint = Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType);
      }
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1020_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1020_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1020_genTpConstraint);
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
        for (BigInteger _1021_tpI = BigInteger.Zero; _1021_tpI < _hi6; _1021_tpI++) {
          DAST._ITypeArgDecl _1022_tp;
          _1022_tp = (@params).Select(_1021_tpI);
          DAST._IType _1023_typeArg;
          RAST._ITypeParamDecl _1024_typeParam;
          DAST._IType _out21;
          RAST._ITypeParamDecl _out22;
          (this).GenTypeParam(_1022_tp, out _out21, out _out22);
          _1023_typeArg = _out21;
          _1024_typeParam = _out22;
          RAST._IType _1025_rType;
          RAST._IType _out23;
          _out23 = (this).GenType(_1023_typeArg, false, false);
          _1025_rType = _out23;
          typeParamsSet = Dafny.Set<DAST._IType>.Union(typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1023_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1025_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1024_typeParam));
        }
      }
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1026_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1027_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1028_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1029_whereConstraints;
      Dafny.ISet<DAST._IType> _out24;
      Dafny.ISequence<RAST._IType> _out25;
      Dafny.ISequence<RAST._ITypeParamDecl> _out26;
      Dafny.ISequence<Dafny.Rune> _out27;
      (this).GenTypeParameters((c).dtor_typeParams, out _out24, out _out25, out _out26, out _out27);
      _1026_typeParamsSet = _out24;
      _1027_rTypeParams = _out25;
      _1028_rTypeParamsDecls = _out26;
      _1029_whereConstraints = _out27;
      Dafny.ISequence<Dafny.Rune> _1030_constrainedTypeParams;
      _1030_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1028_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1031_fields;
      _1031_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1032_fieldInits;
      _1032_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1033_fieldI = BigInteger.Zero; _1033_fieldI < _hi7; _1033_fieldI++) {
        DAST._IField _1034_field;
        _1034_field = ((c).dtor_fields).Select(_1033_fieldI);
        RAST._IType _1035_fieldType;
        RAST._IType _out28;
        _out28 = (this).GenType(((_1034_field).dtor_formal).dtor_typ, false, false);
        _1035_fieldType = _out28;
        Dafny.ISequence<Dafny.Rune> _1036_fieldRustName;
        _1036_fieldRustName = DCOMP.__default.escapeName(((_1034_field).dtor_formal).dtor_name);
        _1031_fields = Dafny.Sequence<RAST._IField>.Concat(_1031_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1036_fieldRustName, _1035_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source45 = (_1034_field).dtor_defaultValue;
        if (_source45.is_Some) {
          DAST._IExpression _1037_e = _source45.dtor_value;
          {
            RAST._IExpr _1038_expr;
            DCOMP._IOwnership _1039___v42;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1040___v43;
            RAST._IExpr _out29;
            DCOMP._IOwnership _out30;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out31;
            (this).GenExpr(_1037_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out29, out _out30, out _out31);
            _1038_expr = _out29;
            _1039___v42 = _out30;
            _1040___v43 = _out31;
            _1032_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1032_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1034_field).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cell::RefCell::new("), (_1038_expr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))))));
          }
          goto after_match2;
        }
        {
          RAST._IExpr _1041_default;
          _1041_default = RAST.__default.std__Default__default;
          _1032_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1032_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1036_fieldRustName, _1041_default)));
        }
      after_match2: ;
      }
      BigInteger _hi8 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1042_typeParamI = BigInteger.Zero; _1042_typeParamI < _hi8; _1042_typeParamI++) {
        DAST._IType _1043_typeArg;
        RAST._ITypeParamDecl _1044_typeParam;
        DAST._IType _out32;
        RAST._ITypeParamDecl _out33;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1042_typeParamI), out _out32, out _out33);
        _1043_typeArg = _out32;
        _1044_typeParam = _out33;
        RAST._IType _1045_rTypeArg;
        RAST._IType _out34;
        _out34 = (this).GenType(_1043_typeArg, false, false);
        _1045_rTypeArg = _out34;
        _1031_fields = Dafny.Sequence<RAST._IField>.Concat(_1031_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1042_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1045_rTypeArg))))));
        _1032_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1032_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1042_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      Dafny.ISequence<Dafny.Rune> _1046_datatypeName;
      _1046_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IStruct _1047_struct;
      _1047_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1046_datatypeName, _1028_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1031_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1047_struct));
      Dafny.ISequence<RAST._IImplMember> _1048_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1049_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out35;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out36;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(path, (c).dtor_attributes))), _1026_typeParamsSet, out _out35, out _out36);
      _1048_implBodyRaw = _out35;
      _1049_traitBodies = _out36;
      Dafny.ISequence<RAST._IImplMember> _1050_implBody;
      _1050_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(RAST.Expr.create_Identifier(_1046_datatypeName), _1032_fieldInits))))), _1048_implBodyRaw);
      RAST._IImpl _1051_i;
      _1051_i = RAST.Impl.create_Impl(_1028_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1046_datatypeName), _1027_rTypeParams), _1029_whereConstraints, _1050_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1051_i)));
      if ((new BigInteger(((c).dtor_superClasses).Count)).Sign == 1) {
        BigInteger _1052_i;
        _1052_i = BigInteger.Zero;
        while ((_1052_i) < (new BigInteger(((c).dtor_superClasses).Count))) {
          DAST._IType _1053_superClass;
          _1053_superClass = ((c).dtor_superClasses).Select(_1052_i);
          DAST._IType _source46 = _1053_superClass;
          if (_source46.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1054_traitPath = _source46.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1055_typeArgs = _source46.dtor_typeArgs;
            DAST._IResolvedType resolved0 = _source46.dtor_resolved;
            if (resolved0.is_Trait) {
              {
                RAST._IType _1056_pathStr;
                RAST._IType _out37;
                _out37 = DCOMP.COMP.GenPath(_1054_traitPath);
                _1056_pathStr = _out37;
                Dafny.ISequence<RAST._IType> _1057_typeArgs;
                Dafny.ISequence<RAST._IType> _out38;
                _out38 = (this).GenTypeArgs(_1055_typeArgs, false, false);
                _1057_typeArgs = _out38;
                Dafny.ISequence<RAST._IImplMember> _1058_body;
                _1058_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_1049_traitBodies).Contains(_1054_traitPath)) {
                  _1058_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1049_traitBodies,_1054_traitPath);
                }
                RAST._IType _1059_genSelfPath;
                RAST._IType _out39;
                _out39 = DCOMP.COMP.GenPath(path);
                _1059_genSelfPath = _out39;
                RAST._IModDecl _1060_x;
                _1060_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1028_rTypeParamsDecls, RAST.Type.create_TypeApp(_1056_pathStr, _1057_typeArgs), RAST.__default.Rc(RAST.Type.create_TypeApp(_1059_genSelfPath, _1027_rTypeParams)), _1029_whereConstraints, _1058_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1060_x));
              }
              goto after_match3;
            }
          }
        after_match3: ;
          _1052_i = (_1052_i) + (BigInteger.One);
        }
      }
      RAST._IImpl _1061_d;
      _1061_d = RAST.Impl.create_ImplFor(_1028_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1046_datatypeName), _1027_rTypeParams), _1029_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(_1046_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new()"))))))));
      Dafny.ISequence<RAST._IModDecl> _1062_defaultImpl;
      _1062_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1061_d));
      RAST._IImpl _1063_p;
      _1063_p = RAST.Impl.create_ImplFor(_1028_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1046_datatypeName), _1027_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), DCOMP.__default.escapeName(((c).dtor_enclosingModule))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")"))))))));
      Dafny.ISequence<RAST._IModDecl> _1064_printImpl;
      _1064_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1063_p));
      RAST._IImpl _1065_pp;
      _1065_pp = RAST.Impl.create_ImplFor(_1028_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cmp::PartialEq")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1046_datatypeName), _1027_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("eq"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.__default.SelfBorrowed)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ptr::eq(self, other)")))))));
      Dafny.ISequence<RAST._IModDecl> _1066_ptrPartialEqImpl;
      _1066_ptrPartialEqImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1065_pp));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(s, _1062_defaultImpl), _1064_printImpl), _1066_ptrPartialEqImpl);
      return s;
    }
    public Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _1067_typeParamsSet;
      _1067_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1068_typeParamDecls;
      _1068_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1069_typeParams;
      _1069_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1070_tpI;
      _1070_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        while ((_1070_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._ITypeArgDecl _1071_tp;
          _1071_tp = ((t).dtor_typeParams).Select(_1070_tpI);
          DAST._IType _1072_typeArg;
          RAST._ITypeParamDecl _1073_typeParamDecl;
          DAST._IType _out40;
          RAST._ITypeParamDecl _out41;
          (this).GenTypeParam(_1071_tp, out _out40, out _out41);
          _1072_typeArg = _out40;
          _1073_typeParamDecl = _out41;
          _1067_typeParamsSet = Dafny.Set<DAST._IType>.Union(_1067_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1072_typeArg));
          _1068_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1068_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1073_typeParamDecl));
          RAST._IType _1074_typeParam;
          RAST._IType _out42;
          _out42 = (this).GenType(_1072_typeArg, false, false);
          _1074_typeParam = _out42;
          _1069_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1069_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1074_typeParam));
          _1070_tpI = (_1070_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1075_fullPath;
      _1075_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1076_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1077___v47;
      Dafny.ISequence<RAST._IImplMember> _out43;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out44;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_1075_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_1075_fullPath, (t).dtor_attributes)), _1067_typeParamsSet, out _out43, out _out44);
      _1076_implBody = _out43;
      _1077___v47 = _out44;
      s = (RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1068_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1069_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1076_implBody)))._ToString(DCOMP.__default.IND);
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1078_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1079_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1080_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1081_whereConstraints;
      Dafny.ISet<DAST._IType> _out45;
      Dafny.ISequence<RAST._IType> _out46;
      Dafny.ISequence<RAST._ITypeParamDecl> _out47;
      Dafny.ISequence<Dafny.Rune> _out48;
      (this).GenTypeParameters((c).dtor_typeParams, out _out45, out _out46, out _out47, out _out48);
      _1078_typeParamsSet = _out45;
      _1079_rTypeParams = _out46;
      _1080_rTypeParamsDecls = _out47;
      _1081_whereConstraints = _out48;
      Dafny.ISequence<Dafny.Rune> _1082_constrainedTypeParams;
      _1082_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1080_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1083_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source47 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      if (_source47.is_Some) {
        RAST._IType _1084_v = _source47.dtor_value;
        _1083_underlyingType = _1084_v;
        goto after_match4;
      }
      RAST._IType _out49;
      _out49 = (this).GenType((c).dtor_base, false, false);
      _1083_underlyingType = _out49;
    after_match4: ;
      DAST._IType _1085_resultingType;
      _1085_resultingType = DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Newtype((c).dtor_base, (c).dtor_range, false, (c).dtor_attributes));
      Dafny.ISequence<Dafny.Rune> _1086_datatypeName;
      _1086_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1086_datatypeName, _1080_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1083_underlyingType))))));
      RAST._IExpr _1087_fnBody;
      _1087_fnBody = RAST.Expr.create_Identifier(_1086_datatypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source48 = (c).dtor_witnessExpr;
      if (_source48.is_Some) {
        DAST._IExpression _1088_e = _source48.dtor_value;
        {
          DAST._IExpression _1089_e;
          if (object.Equals((c).dtor_base, _1085_resultingType)) {
            _1089_e = _1088_e;
          } else {
            _1089_e = DAST.Expression.create_Convert(_1088_e, (c).dtor_base, _1085_resultingType);
          }
          RAST._IExpr _1090_eStr;
          DCOMP._IOwnership _1091___v48;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1092___v49;
          RAST._IExpr _out50;
          DCOMP._IOwnership _out51;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out52;
          (this).GenExpr(_1089_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out50, out _out51, out _out52);
          _1090_eStr = _out50;
          _1091___v48 = _out51;
          _1092___v49 = _out52;
          _1087_fnBody = (_1087_fnBody).Apply1(_1090_eStr);
        }
        goto after_match5;
      }
      {
        _1087_fnBody = (_1087_fnBody).Apply1(RAST.__default.std__Default__default);
      }
    after_match5: ;
      RAST._IImplMember _1093_body;
      _1093_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1087_fnBody)));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1080_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1086_datatypeName), _1079_rTypeParams), _1081_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1093_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1080_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1086_datatypeName), _1079_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1080_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1086_datatypeName), _1079_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1083_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1094_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1095_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1096_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1097_whereConstraints;
      Dafny.ISet<DAST._IType> _out53;
      Dafny.ISequence<RAST._IType> _out54;
      Dafny.ISequence<RAST._ITypeParamDecl> _out55;
      Dafny.ISequence<Dafny.Rune> _out56;
      (this).GenTypeParameters((c).dtor_typeParams, out _out53, out _out54, out _out55, out _out56);
      _1094_typeParamsSet = _out53;
      _1095_rTypeParams = _out54;
      _1096_rTypeParamsDecls = _out55;
      _1097_whereConstraints = _out56;
      Dafny.ISequence<Dafny.Rune> _1098_datatypeName;
      _1098_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1099_ctors;
      _1099_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      BigInteger _hi9 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1100_i = BigInteger.Zero; _1100_i < _hi9; _1100_i++) {
        DAST._IDatatypeCtor _1101_ctor;
        _1101_ctor = ((c).dtor_ctors).Select(_1100_i);
        Dafny.ISequence<RAST._IField> _1102_ctorArgs;
        _1102_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1103_isNumeric;
        _1103_isNumeric = false;
        BigInteger _hi10 = new BigInteger(((_1101_ctor).dtor_args).Count);
        for (BigInteger _1104_j = BigInteger.Zero; _1104_j < _hi10; _1104_j++) {
          DAST._IDatatypeDtor _1105_dtor;
          _1105_dtor = ((_1101_ctor).dtor_args).Select(_1104_j);
          RAST._IType _1106_formalType;
          RAST._IType _out57;
          _out57 = (this).GenType(((_1105_dtor).dtor_formal).dtor_typ, false, false);
          _1106_formalType = _out57;
          Dafny.ISequence<Dafny.Rune> _1107_formalName;
          _1107_formalName = DCOMP.__default.escapeName(((_1105_dtor).dtor_formal).dtor_name);
          if (((_1104_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1107_formalName))) {
            _1103_isNumeric = true;
          }
          if ((((_1104_j).Sign != 0) && (_1103_isNumeric)) && (!(Std.Strings.__default.OfNat(_1104_j)).Equals(_1107_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1107_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1104_j)));
            _1103_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1102_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1102_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1107_formalName, RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1106_formalType))))));
          } else {
            _1102_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1102_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1107_formalName, _1106_formalType))));
          }
        }
        RAST._IFields _1108_namedFields;
        _1108_namedFields = RAST.Fields.create_NamedFields(_1102_ctorArgs);
        if (_1103_isNumeric) {
          _1108_namedFields = (_1108_namedFields).ToNamelessFields();
        }
        _1099_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1099_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1101_ctor).dtor_name), _1108_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1109_selfPath;
      _1109_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1110_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1111_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out58;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out59;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(_1109_selfPath, (c).dtor_attributes))), _1094_typeParamsSet, out _out58, out _out59);
      _1110_implBodyRaw = _out58;
      _1111_traitBodies = _out59;
      Dafny.ISequence<RAST._IImplMember> _1112_implBody;
      _1112_implBody = _1110_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1113_emittedFields;
      _1113_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi11 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1114_i = BigInteger.Zero; _1114_i < _hi11; _1114_i++) {
        DAST._IDatatypeCtor _1115_ctor;
        _1115_ctor = ((c).dtor_ctors).Select(_1114_i);
        BigInteger _hi12 = new BigInteger(((_1115_ctor).dtor_args).Count);
        for (BigInteger _1116_j = BigInteger.Zero; _1116_j < _hi12; _1116_j++) {
          DAST._IDatatypeDtor _1117_dtor;
          _1117_dtor = ((_1115_ctor).dtor_args).Select(_1116_j);
          Dafny.ISequence<Dafny.Rune> _1118_callName;
          _1118_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1117_dtor).dtor_callName, DCOMP.__default.escapeName(((_1117_dtor).dtor_formal).dtor_name));
          if (!((_1113_emittedFields).Contains(_1118_callName))) {
            _1113_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1113_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1118_callName));
            RAST._IType _1119_formalType;
            RAST._IType _out60;
            _out60 = (this).GenType(((_1117_dtor).dtor_formal).dtor_typ, false, false);
            _1119_formalType = _out60;
            Dafny.ISequence<RAST._IMatchCase> _1120_cases;
            _1120_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1121_k = BigInteger.Zero; _1121_k < _hi13; _1121_k++) {
              DAST._IDatatypeCtor _1122_ctor2;
              _1122_ctor2 = ((c).dtor_ctors).Select(_1121_k);
              Dafny.ISequence<Dafny.Rune> _1123_pattern;
              _1123_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1098_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1122_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1124_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1125_hasMatchingField;
              _1125_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1126_patternInner;
              _1126_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1127_isNumeric;
              _1127_isNumeric = false;
              BigInteger _hi14 = new BigInteger(((_1122_ctor2).dtor_args).Count);
              for (BigInteger _1128_l = BigInteger.Zero; _1128_l < _hi14; _1128_l++) {
                DAST._IDatatypeDtor _1129_dtor2;
                _1129_dtor2 = ((_1122_ctor2).dtor_args).Select(_1128_l);
                Dafny.ISequence<Dafny.Rune> _1130_patternName;
                _1130_patternName = DCOMP.__default.escapeName(((_1129_dtor2).dtor_formal).dtor_name);
                if (((_1128_l).Sign == 0) && ((_1130_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1127_isNumeric = true;
                }
                if (_1127_isNumeric) {
                  _1130_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1129_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1128_l)));
                }
                if (object.Equals(((_1117_dtor).dtor_formal).dtor_name, ((_1129_dtor2).dtor_formal).dtor_name)) {
                  _1125_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1130_patternName);
                }
                _1126_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1126_patternInner, _1130_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1127_isNumeric) {
                _1123_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1123_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1126_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1123_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1123_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1126_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1125_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1124_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1125_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1124_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1125_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1124_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _1131_ctorMatch;
              _1131_ctorMatch = RAST.MatchCase.create(_1123_pattern, RAST.Expr.create_RawExpr(_1124_rhs));
              _1120_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1120_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1131_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1120_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1120_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1098_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _1132_methodBody;
            _1132_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1120_cases);
            _1112_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1112_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1118_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1119_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1132_methodBody)))));
          }
        }
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1133_types;
        _1133_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi15 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1134_typeI = BigInteger.Zero; _1134_typeI < _hi15; _1134_typeI++) {
          DAST._IType _1135_typeArg;
          RAST._ITypeParamDecl _1136_rTypeParamDecl;
          DAST._IType _out61;
          RAST._ITypeParamDecl _out62;
          (this).GenTypeParam(((c).dtor_typeParams).Select(_1134_typeI), out _out61, out _out62);
          _1135_typeArg = _out61;
          _1136_rTypeParamDecl = _out62;
          RAST._IType _1137_rTypeArg;
          RAST._IType _out63;
          _out63 = (this).GenType(_1135_typeArg, false, false);
          _1137_rTypeArg = _out63;
          _1133_types = Dafny.Sequence<RAST._IType>.Concat(_1133_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1137_rTypeArg))));
        }
        _1099_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1099_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1138_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1138_tpe);
})), _1133_types)))));
      }
      Dafny.ISequence<RAST._IModDecl> _1139_enumBody;
      _1139_enumBody = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]")), _1098_datatypeName, _1096_rTypeParamsDecls, _1099_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1096_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1098_datatypeName), _1095_rTypeParams), _1097_whereConstraints, _1112_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1140_printImplBodyCases;
      _1140_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1141_i = BigInteger.Zero; _1141_i < _hi16; _1141_i++) {
        DAST._IDatatypeCtor _1142_ctor;
        _1142_ctor = ((c).dtor_ctors).Select(_1141_i);
        Dafny.ISequence<Dafny.Rune> _1143_ctorMatch;
        _1143_ctorMatch = DCOMP.__default.escapeName((_1142_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1144_modulePrefix;
        if (((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) {
          _1144_modulePrefix = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        } else {
          _1144_modulePrefix = Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."));
        }
        Dafny.ISequence<Dafny.Rune> _1145_ctorName;
        _1145_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1144_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1142_ctor).dtor_name));
        if (((new BigInteger((_1145_ctorName).Count)) >= (new BigInteger(13))) && (((_1145_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1145_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1146_printRhs;
        _1146_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1145_ctorName), (((_1142_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        bool _1147_isNumeric;
        _1147_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1148_ctorMatchInner;
        _1148_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi17 = new BigInteger(((_1142_ctor).dtor_args).Count);
        for (BigInteger _1149_j = BigInteger.Zero; _1149_j < _hi17; _1149_j++) {
          DAST._IDatatypeDtor _1150_dtor;
          _1150_dtor = ((_1142_ctor).dtor_args).Select(_1149_j);
          Dafny.ISequence<Dafny.Rune> _1151_patternName;
          _1151_patternName = DCOMP.__default.escapeName(((_1150_dtor).dtor_formal).dtor_name);
          if (((_1149_j).Sign == 0) && ((_1151_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1147_isNumeric = true;
          }
          if (_1147_isNumeric) {
            _1151_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1150_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1149_j)));
          }
          _1148_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1148_ctorMatchInner, _1151_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1149_j).Sign == 1) {
            _1146_printRhs = (_1146_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1146_printRhs = (_1146_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1151_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))));
        }
        if (_1147_isNumeric) {
          _1143_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1143_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1148_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1143_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1143_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1148_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1142_ctor).dtor_hasAnyArgs) {
          _1146_printRhs = (_1146_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1146_printRhs = (_1146_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1140_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1140_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1098_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1143_ctorMatch), RAST.Expr.create_Block(_1146_printRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _1140_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1140_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1098_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1152_defaultConstrainedTypeParams;
      _1152_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1096_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      RAST._IExpr _1153_printImplBody;
      _1153_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1140_printImplBodyCases);
      Dafny.ISequence<RAST._IModDecl> _1154_printImpl;
      _1154_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1096_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1098_datatypeName), _1095_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1096_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1098_datatypeName), _1095_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1153_printImplBody)))))));
      Dafny.ISequence<RAST._IModDecl> _1155_defaultImpl;
      _1155_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      Dafny.ISequence<RAST._IModDecl> _1156_asRefImpl;
      _1156_asRefImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1157_structName;
        _1157_structName = (RAST.Expr.create_Identifier(_1098_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1158_structAssignments;
        _1158_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi18 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1159_i = BigInteger.Zero; _1159_i < _hi18; _1159_i++) {
          DAST._IDatatypeDtor _1160_dtor;
          _1160_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1159_i);
          _1158_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1158_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1160_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1161_defaultConstrainedTypeParams;
        _1161_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1096_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1162_fullType;
        _1162_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1098_datatypeName), _1095_rTypeParams);
        _1155_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1161_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1162_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1162_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1157_structName, _1158_structAssignments))))))));
        _1156_asRefImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1096_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_1162_fullType), RAST.Type.create_Borrowed(_1162_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self)))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(_1139_enumBody, _1154_printImpl), _1155_defaultImpl), _1156_asRefImpl);
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
        } else {
          r = RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"));
        }
        BigInteger _hi19 = new BigInteger((p).Count);
        for (BigInteger _1163_i = BigInteger.Zero; _1163_i < _hi19; _1163_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1163_i))));
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
        } else {
          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"));
        }
        BigInteger _hi20 = new BigInteger((p).Count);
        for (BigInteger _1164_i = BigInteger.Zero; _1164_i < _hi20; _1164_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1164_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding, bool inFn)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger((args).Count)).Sign == 1) {
        BigInteger _1165_i;
        _1165_i = BigInteger.Zero;
        while ((_1165_i) < (new BigInteger((args).Count))) {
          RAST._IType _1166_genTp;
          RAST._IType _out64;
          _out64 = (this).GenType((args).Select(_1165_i), inBinding, inFn);
          _1166_genTp = _out64;
          s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1166_genTp));
          _1165_i = (_1165_i) + (BigInteger.One);
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
      if (_source49.is_Path) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1167_p = _source49.dtor_Path_a0;
        Dafny.ISequence<DAST._IType> _1168_args = _source49.dtor_typeArgs;
        DAST._IResolvedType _1169_resolved = _source49.dtor_resolved;
        {
          RAST._IType _1170_t;
          RAST._IType _out65;
          _out65 = DCOMP.COMP.GenPath(_1167_p);
          _1170_t = _out65;
          Dafny.ISequence<RAST._IType> _1171_typeArgs;
          Dafny.ISequence<RAST._IType> _out66;
          _out66 = (this).GenTypeArgs(_1168_args, inBinding, inFn);
          _1171_typeArgs = _out66;
          s = RAST.Type.create_TypeApp(_1170_t, _1171_typeArgs);
          DAST._IResolvedType _source50 = _1169_resolved;
          if (_source50.is_Datatype) {
            DAST._IDatatypeType datatypeType0 = _source50.dtor_datatypeType;
            Dafny.ISequence<DAST._IAttribute> _1172_attributes = datatypeType0.dtor_attributes;
            {
              if ((this).IsRcWrapped(_1172_attributes)) {
                s = RAST.__default.Rc(s);
              }
            }
            goto after_match7;
          }
          if (_source50.is_Trait) {
            {
              if ((_1167_p).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc<dyn ::std::any::Any>"));
              } else {
                if (inBinding) {
                  s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
                } else {
                  s = RAST.Type.create_ImplType(s);
                }
              }
            }
            goto after_match7;
          }
          DAST._IType _1173_t = _source50.dtor_baseType;
          DAST._INewtypeRange _1174_range = _source50.dtor_range;
          bool _1175_erased = _source50.dtor_erase;
          Dafny.ISequence<DAST._IAttribute> _1176_attributes = _source50.dtor_attributes;
          {
            if (_1175_erased) {
              Std.Wrappers._IOption<RAST._IType> _source51 = DCOMP.COMP.NewtypeToRustType(_1173_t, _1174_range);
              if (_source51.is_Some) {
                RAST._IType _1177_v = _source51.dtor_value;
                s = _1177_v;
                goto after_match8;
              }
            after_match8: ;
            }
          }
        after_match7: ;
        }
        goto after_match6;
      }
      if (_source49.is_Nullable) {
        DAST._IType _1178_inner = _source49.dtor_Nullable_a0;
        {
          RAST._IType _1179_innerExpr;
          RAST._IType _out67;
          _out67 = (this).GenType(_1178_inner, inBinding, inFn);
          _1179_innerExpr = _out67;
          s = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::option::Option")), Dafny.Sequence<RAST._IType>.FromElements(_1179_innerExpr));
        }
        goto after_match6;
      }
      if (_source49.is_Tuple) {
        Dafny.ISequence<DAST._IType> _1180_types = _source49.dtor_Tuple_a0;
        {
          Dafny.ISequence<RAST._IType> _1181_args;
          _1181_args = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _1182_i;
          _1182_i = BigInteger.Zero;
          while ((_1182_i) < (new BigInteger((_1180_types).Count))) {
            RAST._IType _1183_generated;
            RAST._IType _out68;
            _out68 = (this).GenType((_1180_types).Select(_1182_i), inBinding, inFn);
            _1183_generated = _out68;
            _1181_args = Dafny.Sequence<RAST._IType>.Concat(_1181_args, Dafny.Sequence<RAST._IType>.FromElements(_1183_generated));
            _1182_i = (_1182_i) + (BigInteger.One);
          }
          if ((new BigInteger((_1180_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) {
            s = RAST.Type.create_TupleType(_1181_args);
          } else {
            s = RAST.__default.SystemTupleType(_1181_args);
          }
        }
        goto after_match6;
      }
      if (_source49.is_Array) {
        DAST._IType _1184_element = _source49.dtor_element;
        BigInteger _1185_dims = _source49.dtor_dims;
        {
          RAST._IType _1186_elem;
          RAST._IType _out69;
          _out69 = (this).GenType(_1184_element, inBinding, inFn);
          _1186_elem = _out69;
          s = _1186_elem;
          BigInteger _1187_i;
          _1187_i = BigInteger.Zero;
          while ((_1187_i) < (_1185_dims)) {
            s = RAST.__default.Rc(RAST.__default.RefCell(RAST.__default.Vec(s)));
            _1187_i = (_1187_i) + (BigInteger.One);
          }
        }
        goto after_match6;
      }
      if (_source49.is_Seq) {
        DAST._IType _1188_element = _source49.dtor_element;
        {
          RAST._IType _1189_elem;
          RAST._IType _out70;
          _out70 = (this).GenType(_1188_element, inBinding, inFn);
          _1189_elem = _out70;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1189_elem));
        }
        goto after_match6;
      }
      if (_source49.is_Set) {
        DAST._IType _1190_element = _source49.dtor_element;
        {
          RAST._IType _1191_elem;
          RAST._IType _out71;
          _out71 = (this).GenType(_1190_element, inBinding, inFn);
          _1191_elem = _out71;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1191_elem));
        }
        goto after_match6;
      }
      if (_source49.is_Multiset) {
        DAST._IType _1192_element = _source49.dtor_element;
        {
          RAST._IType _1193_elem;
          RAST._IType _out72;
          _out72 = (this).GenType(_1192_element, inBinding, inFn);
          _1193_elem = _out72;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1193_elem));
        }
        goto after_match6;
      }
      if (_source49.is_Map) {
        DAST._IType _1194_key = _source49.dtor_key;
        DAST._IType _1195_value = _source49.dtor_value;
        {
          RAST._IType _1196_keyType;
          RAST._IType _out73;
          _out73 = (this).GenType(_1194_key, inBinding, inFn);
          _1196_keyType = _out73;
          RAST._IType _1197_valueType;
          RAST._IType _out74;
          _out74 = (this).GenType(_1195_value, inBinding, inFn);
          _1197_valueType = _out74;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1196_keyType, _1197_valueType));
        }
        goto after_match6;
      }
      if (_source49.is_MapBuilder) {
        DAST._IType _1198_key = _source49.dtor_key;
        DAST._IType _1199_value = _source49.dtor_value;
        {
          RAST._IType _1200_keyType;
          RAST._IType _out75;
          _out75 = (this).GenType(_1198_key, inBinding, inFn);
          _1200_keyType = _out75;
          RAST._IType _1201_valueType;
          RAST._IType _out76;
          _out76 = (this).GenType(_1199_value, inBinding, inFn);
          _1201_valueType = _out76;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1200_keyType, _1201_valueType));
        }
        goto after_match6;
      }
      if (_source49.is_SetBuilder) {
        DAST._IType _1202_elem = _source49.dtor_element;
        {
          RAST._IType _1203_elemType;
          RAST._IType _out77;
          _out77 = (this).GenType(_1202_elem, inBinding, inFn);
          _1203_elemType = _out77;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1203_elemType));
        }
        goto after_match6;
      }
      if (_source49.is_Arrow) {
        Dafny.ISequence<DAST._IType> _1204_args = _source49.dtor_args;
        DAST._IType _1205_result = _source49.dtor_result;
        {
          Dafny.ISequence<RAST._IType> _1206_argTypes;
          _1206_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _1207_i;
          _1207_i = BigInteger.Zero;
          while ((_1207_i) < (new BigInteger((_1204_args).Count))) {
            RAST._IType _1208_generated;
            RAST._IType _out78;
            _out78 = (this).GenType((_1204_args).Select(_1207_i), inBinding, true);
            _1208_generated = _out78;
            _1206_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1206_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1208_generated)));
            _1207_i = (_1207_i) + (BigInteger.One);
          }
          RAST._IType _1209_resultType;
          RAST._IType _out79;
          _out79 = (this).GenType(_1205_result, inBinding, (inFn) || (inBinding));
          _1209_resultType = _out79;
          s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1206_argTypes, _1209_resultType)));
        }
        goto after_match6;
      }
      if (_source49.is_TypeArg) {
        Dafny.ISequence<Dafny.Rune> _h100 = _source49.dtor_TypeArg_a0;
        Dafny.ISequence<Dafny.Rune> _1210_name = _h100;
        s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1210_name));
        goto after_match6;
      }
      if (_source49.is_Primitive) {
        DAST._IPrimitive _1211_p = _source49.dtor_Primitive_a0;
        {
          DAST._IPrimitive _source52 = _1211_p;
          if (_source52.is_Int) {
            s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
            goto after_match9;
          }
          if (_source52.is_Real) {
            s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
            goto after_match9;
          }
          if (_source52.is_String) {
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
            goto after_match9;
          }
          if (_source52.is_Bool) {
            s = RAST.Type.create_Bool();
            goto after_match9;
          }
          s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
        after_match9: ;
        }
        goto after_match6;
      }
      Dafny.ISequence<Dafny.Rune> _1212_v = _source49.dtor_Passthrough_a0;
      s = RAST.__default.RawType(_1212_v);
    after_match6: ;
      return s;
    }
    public void GenClassImplBody(Dafny.ISequence<DAST._IMethod> body, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams, out Dafny.ISequence<RAST._IImplMember> s, out Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> traitBodies)
    {
      s = Dafny.Sequence<RAST._IImplMember>.Empty;
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Empty;
      s = Dafny.Sequence<RAST._IImplMember>.FromElements();
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements();
      BigInteger _hi21 = new BigInteger((body).Count);
      for (BigInteger _1213_i = BigInteger.Zero; _1213_i < _hi21; _1213_i++) {
        DAST._IMethod _source53 = (body).Select(_1213_i);
        DAST._IMethod _1214_m = _source53;
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source54 = (_1214_m).dtor_overridingPath;
          if (_source54.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1215_p = _source54.dtor_value;
            {
              Dafny.ISequence<RAST._IImplMember> _1216_existing;
              _1216_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
              if ((traitBodies).Contains(_1215_p)) {
                _1216_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1215_p);
              }
              RAST._IImplMember _1217_genMethod;
              RAST._IImplMember _out80;
              _out80 = (this).GenMethod(_1214_m, true, enclosingType, enclosingTypeParams);
              _1217_genMethod = _out80;
              _1216_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1216_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1217_genMethod));
              traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1215_p, _1216_existing)));
            }
            goto after_match11;
          }
          {
            RAST._IImplMember _1218_generated;
            RAST._IImplMember _out81;
            _out81 = (this).GenMethod(_1214_m, forTrait, enclosingType, enclosingTypeParams);
            _1218_generated = _out81;
            s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1218_generated));
          }
        after_match11: ;
        }
      after_match10: ;
      }
    }
    public Dafny.ISequence<RAST._IFormal> GenParams(Dafny.ISequence<DAST._IFormal> @params)
    {
      Dafny.ISequence<RAST._IFormal> s = Dafny.Sequence<RAST._IFormal>.Empty;
      s = Dafny.Sequence<RAST._IFormal>.FromElements();
      BigInteger _hi22 = new BigInteger((@params).Count);
      for (BigInteger _1219_i = BigInteger.Zero; _1219_i < _hi22; _1219_i++) {
        DAST._IFormal _1220_param;
        _1220_param = (@params).Select(_1219_i);
        RAST._IType _1221_paramType;
        RAST._IType _out82;
        _out82 = (this).GenType((_1220_param).dtor_typ, false, false);
        _1221_paramType = _out82;
        if ((!((_1221_paramType).CanReadWithoutClone())) && (!((_1220_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1221_paramType = RAST.Type.create_Borrowed(_1221_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_1220_param).dtor_name), _1221_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1222_params;
      Dafny.ISequence<RAST._IFormal> _out83;
      _out83 = (this).GenParams((m).dtor_params);
      _1222_params = _out83;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1223_paramNames;
      _1223_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1224_paramTypes;
      _1224_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi23 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1225_paramI = BigInteger.Zero; _1225_paramI < _hi23; _1225_paramI++) {
        DAST._IFormal _1226_dafny__formal;
        _1226_dafny__formal = ((m).dtor_params).Select(_1225_paramI);
        RAST._IFormal _1227_formal;
        _1227_formal = (_1222_params).Select(_1225_paramI);
        Dafny.ISequence<Dafny.Rune> _1228_name;
        _1228_name = (_1227_formal).dtor_name;
        _1223_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1223_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1228_name));
        _1224_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1224_paramTypes, _1228_name, (_1227_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1229_fnName;
      _1229_fnName = DCOMP.__default.escapeName((m).dtor_name);
      Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1230_selfIdentifier;
      _1230_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1231_selfId;
        _1231_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((_1229_fnName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_ctor"))) {
          _1231_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        if (forTrait) {
          RAST._IFormal _1232_selfFormal;
          _1232_selfFormal = RAST.Formal.selfBorrowedMut;
          _1222_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1232_selfFormal), _1222_params);
        } else {
          RAST._IType _1233_tpe;
          RAST._IType _out84;
          _out84 = (this).GenType(enclosingType, false, false);
          _1233_tpe = _out84;
          if (!((_1233_tpe).CanReadWithoutClone())) {
            _1233_tpe = RAST.Type.create_Borrowed(_1233_tpe);
          }
          _1222_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1231_selfId, _1233_tpe)), _1222_params);
        }
        _1230_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1231_selfId);
      }
      Dafny.ISequence<RAST._IType> _1234_retTypeArgs;
      _1234_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1235_typeI;
      _1235_typeI = BigInteger.Zero;
      while ((_1235_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1236_typeExpr;
        RAST._IType _out85;
        _out85 = (this).GenType(((m).dtor_outTypes).Select(_1235_typeI), false, false);
        _1236_typeExpr = _out85;
        _1234_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1234_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1236_typeExpr));
        _1235_typeI = (_1235_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1237_visibility;
      _1237_visibility = RAST.Visibility.create_PUB();
      Dafny.ISequence<DAST._ITypeArgDecl> _1238_typeParamsFiltered;
      _1238_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi24 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1239_typeParamI = BigInteger.Zero; _1239_typeParamI < _hi24; _1239_typeParamI++) {
        DAST._ITypeArgDecl _1240_typeParam;
        _1240_typeParam = ((m).dtor_typeParams).Select(_1239_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1240_typeParam).dtor_name)))) {
          _1238_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1238_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1240_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1241_typeParams;
      _1241_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1238_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi25 = new BigInteger((_1238_typeParamsFiltered).Count);
        for (BigInteger _1242_i = BigInteger.Zero; _1242_i < _hi25; _1242_i++) {
          DAST._IType _1243_typeArg;
          RAST._ITypeParamDecl _1244_rTypeParamDecl;
          DAST._IType _out86;
          RAST._ITypeParamDecl _out87;
          (this).GenTypeParam((_1238_typeParamsFiltered).Select(_1242_i), out _out86, out _out87);
          _1243_typeArg = _out86;
          _1244_rTypeParamDecl = _out87;
          RAST._ITypeParamDecl _1245_dt__update__tmp_h0 = _1244_rTypeParamDecl;
          Dafny.ISequence<RAST._IType> _1246_dt__update_hconstraints_h0 = Dafny.Sequence<RAST._IType>.Concat((_1244_rTypeParamDecl).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
          _1244_rTypeParamDecl = RAST.TypeParamDecl.create((_1245_dt__update__tmp_h0).dtor_content, _1246_dt__update_hconstraints_h0);
          _1241_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1241_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1244_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1247_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1248_env = DCOMP.Environment.Default();
      RAST._IExpr _1249_preBody;
      _1249_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      if ((m).dtor_hasBody) {
        RAST._IExpr _1250_earlyReturn;
        _1250_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source55 = (m).dtor_outVars;
        if (_source55.is_Some) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1251_outVars = _source55.dtor_value;
          {
            Dafny.ISequence<RAST._IExpr> _1252_tupleArgs;
            _1252_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi26 = new BigInteger((_1251_outVars).Count);
            for (BigInteger _1253_outI = BigInteger.Zero; _1253_outI < _hi26; _1253_outI++) {
              Dafny.ISequence<Dafny.Rune> _1254_outVar;
              _1254_outVar = (_1251_outVars).Select(_1253_outI);
              RAST._IType _1255_outType;
              RAST._IType _out88;
              _out88 = (this).GenType(((m).dtor_outTypes).Select(_1253_outI), false, false);
              _1255_outType = _out88;
              Dafny.ISequence<Dafny.Rune> _1256_outName;
              _1256_outName = DCOMP.__default.escapeName((_1254_outVar));
              _1223_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1223_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1256_outName));
              RAST._IType _1257_outMaybeType;
              if ((_1255_outType).CanReadWithoutClone()) {
                _1257_outMaybeType = _1255_outType;
              } else {
                _1257_outMaybeType = RAST.Type.create_Borrowed(_1255_outType);
              }
              _1224_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1224_paramTypes, _1256_outName, _1257_outMaybeType);
              RAST._IExpr _1258_outVarReturn;
              DCOMP._IOwnership _1259___v53;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1260___v54;
              RAST._IExpr _out89;
              DCOMP._IOwnership _out90;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out91;
              (this).GenExpr(DAST.Expression.create_Ident((_1254_outVar)), Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1256_outName), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>, RAST._IType>(_1256_outName, _1257_outMaybeType))), DCOMP.Ownership.create_OwnershipOwned(), out _out89, out _out90, out _out91);
              _1258_outVarReturn = _out89;
              _1259___v53 = _out90;
              _1260___v54 = _out91;
              _1252_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1252_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1258_outVarReturn));
            }
            if ((new BigInteger((_1252_tupleArgs).Count)) == (BigInteger.One)) {
              _1250_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1252_tupleArgs).Select(BigInteger.Zero)));
            } else {
              _1250_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1252_tupleArgs)));
            }
          }
          goto after_match12;
        }
      after_match12: ;
        _1248_env = DCOMP.Environment.create(_1223_paramNames, _1224_paramTypes);
        RAST._IExpr _1261_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1262___v55;
        DCOMP._IEnvironment _1263___v56;
        RAST._IExpr _out92;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out93;
        DCOMP._IEnvironment _out94;
        (this).GenStmts((m).dtor_body, _1230_selfIdentifier, _1248_env, true, _1250_earlyReturn, out _out92, out _out93, out _out94);
        _1261_body = _out92;
        _1262___v55 = _out93;
        _1263___v56 = _out94;
        _1247_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1249_preBody).Then(_1261_body));
      } else {
        _1248_env = DCOMP.Environment.create(_1223_paramNames, _1224_paramTypes);
        _1247_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1237_visibility, RAST.Fn.create(_1229_fnName, _1241_typeParams, _1222_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1234_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1234_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1234_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1247_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1264_declarations;
      _1264_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1265_i;
      _1265_i = BigInteger.Zero;
      newEnv = env;
      while ((_1265_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _1266_stmt;
        _1266_stmt = (stmts).Select(_1265_i);
        RAST._IExpr _1267_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1268_recIdents;
        DCOMP._IEnvironment _1269_newEnv2;
        RAST._IExpr _out95;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out96;
        DCOMP._IEnvironment _out97;
        (this).GenStmt(_1266_stmt, selfIdent, newEnv, (isLast) && ((_1265_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out95, out _out96, out _out97);
        _1267_stmtExpr = _out95;
        _1268_recIdents = _out96;
        _1269_newEnv2 = _out97;
        newEnv = _1269_newEnv2;
        DAST._IStatement _source56 = _1266_stmt;
        if (_source56.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1270_name = _source56.dtor_name;
          {
            _1264_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1264_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_1270_name)));
          }
          goto after_match13;
        }
      after_match13: ;
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1268_recIdents, _1264_declarations));
        generated = (generated).Then(_1267_stmtExpr);
        _1265_i = (_1265_i) + (BigInteger.One);
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
      if (_source57.is_Ident) {
        Dafny.ISequence<Dafny.Rune> ident0 = _source57.dtor_ident;
        Dafny.ISequence<Dafny.Rune> _1271_id = ident0;
        {
          Dafny.ISequence<Dafny.Rune> _1272_idRust;
          _1272_idRust = DCOMP.__default.escapeName(_1271_id);
          if (((env).IsBorrowed(_1272_idRust)) || ((env).IsBorrowedMut(_1272_idRust))) {
            generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1272_idRust), rhs);
          } else {
            generated = RAST.__default.AssignVar(_1272_idRust, rhs);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1272_idRust);
          needsIIFE = false;
        }
        goto after_match14;
      }
      if (_source57.is_Select) {
        DAST._IExpression _1273_on = _source57.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _1274_field = _source57.dtor_field;
        {
          Dafny.ISequence<Dafny.Rune> _1275_fieldName;
          _1275_fieldName = DCOMP.__default.escapeName(_1274_field);
          RAST._IExpr _1276_onExpr;
          DCOMP._IOwnership _1277_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1278_recIdents;
          RAST._IExpr _out98;
          DCOMP._IOwnership _out99;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out100;
          (this).GenExpr(_1273_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out98, out _out99, out _out100);
          _1276_onExpr = _out98;
          _1277_onOwned = _out99;
          _1278_recIdents = _out100;
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*("), (_1276_onExpr)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _1275_fieldName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()) = ")), (rhs)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";")));
          readIdents = _1278_recIdents;
          needsIIFE = true;
        }
        goto after_match14;
      }
      DAST._IExpression _1279_on = _source57.dtor_expr;
      Dafny.ISequence<DAST._IExpression> _1280_indices = _source57.dtor_indices;
      {
        RAST._IExpr _1281_onExpr;
        DCOMP._IOwnership _1282_onOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1283_recIdents;
        RAST._IExpr _out101;
        DCOMP._IOwnership _out102;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out103;
        (this).GenExpr(_1279_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out101, out _out102, out _out103);
        _1281_onExpr = _out101;
        _1282_onOwned = _out102;
        _1283_recIdents = _out103;
        readIdents = _1283_recIdents;
        Dafny.ISequence<Dafny.Rune> _1284_r;
        _1284_r = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
        BigInteger _1285_i;
        _1285_i = BigInteger.Zero;
        while ((_1285_i) < (new BigInteger((_1280_indices).Count))) {
          RAST._IExpr _1286_idx;
          DCOMP._IOwnership _1287___v60;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1288_recIdentsIdx;
          RAST._IExpr _out104;
          DCOMP._IOwnership _out105;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out106;
          (this).GenExpr((_1280_indices).Select(_1285_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out104, out _out105, out _out106);
          _1286_idx = _out104;
          _1287___v60 = _out105;
          _1288_recIdentsIdx = _out106;
          _1284_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1284_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let __idx")), Std.Strings.__default.OfNat(_1285_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = <usize as ::dafny_runtime::NumCast>::from(")), (_1286_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap();\n"));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1288_recIdentsIdx);
          _1285_i = (_1285_i) + (BigInteger.One);
        }
        _1284_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1284_r, (_1281_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()"));
        _1285_i = BigInteger.Zero;
        while ((_1285_i) < (new BigInteger((_1280_indices).Count))) {
          _1284_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1284_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[__idx")), Std.Strings.__default.OfNat(_1285_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
          _1285_i = (_1285_i) + (BigInteger.One);
        }
        generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1284_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), (rhs)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n}")));
        needsIIFE = true;
      }
    after_match14: ;
    }
    public void GenStmt(DAST._IStatement stmt, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source58 = stmt;
      if (_source58.is_DeclareVar) {
        Dafny.ISequence<Dafny.Rune> _1289_name = _source58.dtor_name;
        DAST._IType _1290_typ = _source58.dtor_typ;
        Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source58.dtor_maybeValue;
        if (maybeValue0.is_Some) {
          DAST._IExpression _1291_expression = maybeValue0.dtor_value;
          {
            RAST._IType _1292_tpe;
            RAST._IType _out107;
            _out107 = (this).GenType(_1290_typ, true, false);
            _1292_tpe = _out107;
            RAST._IExpr _1293_expr;
            DCOMP._IOwnership _1294_exprOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1295_recIdents;
            RAST._IExpr _out108;
            DCOMP._IOwnership _out109;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out110;
            (this).GenExpr(_1291_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out108, out _out109, out _out110);
            _1293_expr = _out108;
            _1294_exprOwnership = _out109;
            _1295_recIdents = _out110;
            readIdents = _1295_recIdents;
            generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_1289_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1292_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1293_expr));
            newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_1289_name), _1292_tpe);
          }
          goto after_match15;
        }
      }
      if (_source58.is_DeclareVar) {
        Dafny.ISequence<Dafny.Rune> _1296_name = _source58.dtor_name;
        DAST._IType _1297_typ = _source58.dtor_typ;
        Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source58.dtor_maybeValue;
        if (maybeValue1.is_None) {
          {
            DAST._IStatement _1298_newStmt;
            _1298_newStmt = DAST.Statement.create_DeclareVar(_1296_name, _1297_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1297_typ)));
            RAST._IExpr _out111;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out112;
            DCOMP._IEnvironment _out113;
            (this).GenStmt(_1298_newStmt, selfIdent, env, isLast, earlyReturn, out _out111, out _out112, out _out113);
            generated = _out111;
            readIdents = _out112;
            newEnv = _out113;
          }
          goto after_match15;
        }
      }
      if (_source58.is_Assign) {
        DAST._IAssignLhs _1299_lhs = _source58.dtor_lhs;
        DAST._IExpression _1300_expression = _source58.dtor_value;
        {
          RAST._IExpr _1301_exprGen;
          DCOMP._IOwnership _1302___v61;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1303_exprIdents;
          RAST._IExpr _out114;
          DCOMP._IOwnership _out115;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
          (this).GenExpr(_1300_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out114, out _out115, out _out116);
          _1301_exprGen = _out114;
          _1302___v61 = _out115;
          _1303_exprIdents = _out116;
          if ((_1299_lhs).is_Ident) {
            Dafny.ISequence<Dafny.Rune> _1304_rustId;
            _1304_rustId = DCOMP.__default.escapeName(((_1299_lhs).dtor_ident));
            Std.Wrappers._IOption<RAST._IType> _1305_tpe;
            _1305_tpe = (env).GetType(_1304_rustId);
          }
          RAST._IExpr _1306_lhsGen;
          bool _1307_needsIIFE;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1308_recIdents;
          DCOMP._IEnvironment _1309_resEnv;
          RAST._IExpr _out117;
          bool _out118;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out119;
          DCOMP._IEnvironment _out120;
          (this).GenAssignLhs(_1299_lhs, _1301_exprGen, selfIdent, env, out _out117, out _out118, out _out119, out _out120);
          _1306_lhsGen = _out117;
          _1307_needsIIFE = _out118;
          _1308_recIdents = _out119;
          _1309_resEnv = _out120;
          generated = _1306_lhsGen;
          newEnv = _1309_resEnv;
          if (_1307_needsIIFE) {
            generated = RAST.Expr.create_Block(generated);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1308_recIdents, _1303_exprIdents);
        }
        goto after_match15;
      }
      if (_source58.is_If) {
        DAST._IExpression _1310_cond = _source58.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _1311_thnDafny = _source58.dtor_thn;
        Dafny.ISequence<DAST._IStatement> _1312_elsDafny = _source58.dtor_els;
        {
          RAST._IExpr _1313_cond;
          DCOMP._IOwnership _1314___v62;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1315_recIdents;
          RAST._IExpr _out121;
          DCOMP._IOwnership _out122;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out123;
          (this).GenExpr(_1310_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out121, out _out122, out _out123);
          _1313_cond = _out121;
          _1314___v62 = _out122;
          _1315_recIdents = _out123;
          Dafny.ISequence<Dafny.Rune> _1316_condString;
          _1316_condString = (_1313_cond)._ToString(DCOMP.__default.IND);
          readIdents = _1315_recIdents;
          RAST._IExpr _1317_thn;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1318_thnIdents;
          DCOMP._IEnvironment _1319_thnEnv;
          RAST._IExpr _out124;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out125;
          DCOMP._IEnvironment _out126;
          (this).GenStmts(_1311_thnDafny, selfIdent, env, isLast, earlyReturn, out _out124, out _out125, out _out126);
          _1317_thn = _out124;
          _1318_thnIdents = _out125;
          _1319_thnEnv = _out126;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1318_thnIdents);
          RAST._IExpr _1320_els;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1321_elsIdents;
          DCOMP._IEnvironment _1322_elsEnv;
          RAST._IExpr _out127;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out128;
          DCOMP._IEnvironment _out129;
          (this).GenStmts(_1312_elsDafny, selfIdent, env, isLast, earlyReturn, out _out127, out _out128, out _out129);
          _1320_els = _out127;
          _1321_elsIdents = _out128;
          _1322_elsEnv = _out129;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1321_elsIdents);
          newEnv = env;
          generated = RAST.Expr.create_IfExpr(_1313_cond, _1317_thn, _1320_els);
        }
        goto after_match15;
      }
      if (_source58.is_Labeled) {
        Dafny.ISequence<Dafny.Rune> _1323_lbl = _source58.dtor_lbl;
        Dafny.ISequence<DAST._IStatement> _1324_body = _source58.dtor_body;
        {
          RAST._IExpr _1325_body;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1326_bodyIdents;
          DCOMP._IEnvironment _1327_env2;
          RAST._IExpr _out130;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
          DCOMP._IEnvironment _out132;
          (this).GenStmts(_1324_body, selfIdent, env, isLast, earlyReturn, out _out130, out _out131, out _out132);
          _1325_body = _out130;
          _1326_bodyIdents = _out131;
          _1327_env2 = _out132;
          readIdents = _1326_bodyIdents;
          generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1323_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1325_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
          newEnv = env;
        }
        goto after_match15;
      }
      if (_source58.is_While) {
        DAST._IExpression _1328_cond = _source58.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _1329_body = _source58.dtor_body;
        {
          RAST._IExpr _1330_cond;
          DCOMP._IOwnership _1331___v63;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1332_recIdents;
          RAST._IExpr _out133;
          DCOMP._IOwnership _out134;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
          (this).GenExpr(_1328_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out133, out _out134, out _out135);
          _1330_cond = _out133;
          _1331___v63 = _out134;
          _1332_recIdents = _out135;
          readIdents = _1332_recIdents;
          RAST._IExpr _1333_bodyExpr;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1334_bodyIdents;
          DCOMP._IEnvironment _1335_bodyEnv;
          RAST._IExpr _out136;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
          DCOMP._IEnvironment _out138;
          (this).GenStmts(_1329_body, selfIdent, env, false, earlyReturn, out _out136, out _out137, out _out138);
          _1333_bodyExpr = _out136;
          _1334_bodyIdents = _out137;
          _1335_bodyEnv = _out138;
          newEnv = env;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1334_bodyIdents);
          generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1330_cond), _1333_bodyExpr);
        }
        goto after_match15;
      }
      if (_source58.is_Foreach) {
        Dafny.ISequence<Dafny.Rune> _1336_boundName = _source58.dtor_boundName;
        DAST._IType _1337_boundType = _source58.dtor_boundType;
        DAST._IExpression _1338_over = _source58.dtor_over;
        Dafny.ISequence<DAST._IStatement> _1339_body = _source58.dtor_body;
        {
          RAST._IExpr _1340_over;
          DCOMP._IOwnership _1341___v64;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1342_recIdents;
          RAST._IExpr _out139;
          DCOMP._IOwnership _out140;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out141;
          (this).GenExpr(_1338_over, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out139, out _out140, out _out141);
          _1340_over = _out139;
          _1341___v64 = _out140;
          _1342_recIdents = _out141;
          RAST._IType _1343_boundTpe;
          RAST._IType _out142;
          _out142 = (this).GenType(_1337_boundType, false, false);
          _1343_boundTpe = _out142;
          readIdents = _1342_recIdents;
          Dafny.ISequence<Dafny.Rune> _1344_boundRName;
          _1344_boundRName = DCOMP.__default.escapeName(_1336_boundName);
          RAST._IExpr _1345_bodyExpr;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1346_bodyIdents;
          DCOMP._IEnvironment _1347_bodyEnv;
          RAST._IExpr _out143;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
          DCOMP._IEnvironment _out145;
          (this).GenStmts(_1339_body, selfIdent, (env).AddAssigned(_1344_boundRName, _1343_boundTpe), false, earlyReturn, out _out143, out _out144, out _out145);
          _1345_bodyExpr = _out143;
          _1346_bodyIdents = _out144;
          _1347_bodyEnv = _out145;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1346_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1344_boundRName));
          newEnv = env;
          generated = RAST.Expr.create_For(_1344_boundRName, _1340_over, _1345_bodyExpr);
        }
        goto after_match15;
      }
      if (_source58.is_Break) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1348_toLabel = _source58.dtor_toLabel;
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source59 = _1348_toLabel;
          if (_source59.is_Some) {
            Dafny.ISequence<Dafny.Rune> _1349_lbl = _source59.dtor_value;
            {
              generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1349_lbl)));
            }
            goto after_match16;
          }
          {
            generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
          }
        after_match16: ;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
        goto after_match15;
      }
      if (_source58.is_TailRecursive) {
        Dafny.ISequence<DAST._IStatement> _1350_body = _source58.dtor_body;
        {
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
            generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
          }
          newEnv = env;
          BigInteger _hi27 = new BigInteger(((env).dtor_names).Count);
          for (BigInteger _1351_paramI = BigInteger.Zero; _1351_paramI < _hi27; _1351_paramI++) {
            Dafny.ISequence<Dafny.Rune> _1352_param;
            _1352_param = ((env).dtor_names).Select(_1351_paramI);
            RAST._IExpr _1353_paramInit;
            DCOMP._IOwnership _1354___v65;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1355___v66;
            RAST._IExpr _out146;
            DCOMP._IOwnership _out147;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out148;
            (this).GenIdent(_1352_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out146, out _out147, out _out148);
            _1353_paramInit = _out146;
            _1354___v65 = _out147;
            _1355___v66 = _out148;
            generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1352_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1353_paramInit)));
            if (((env).dtor_types).Contains(_1352_param)) {
              RAST._IType _1356_declaredType;
              _1356_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1352_param)).ToOwned();
              newEnv = (newEnv).AddAssigned(_1352_param, _1356_declaredType);
            }
          }
          RAST._IExpr _1357_bodyExpr;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1358_bodyIdents;
          DCOMP._IEnvironment _1359_bodyEnv;
          RAST._IExpr _out149;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out150;
          DCOMP._IEnvironment _out151;
          (this).GenStmts(_1350_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), newEnv, false, earlyReturn, out _out149, out _out150, out _out151);
          _1357_bodyExpr = _out149;
          _1358_bodyIdents = _out150;
          _1359_bodyEnv = _out151;
          readIdents = _1358_bodyIdents;
          generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1357_bodyExpr)));
        }
        goto after_match15;
      }
      if (_source58.is_JumpTailCallStart) {
        {
          generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
        goto after_match15;
      }
      if (_source58.is_Call) {
        DAST._IExpression _1360_on = _source58.dtor_on;
        DAST._ICallName _1361_name = _source58.dtor_callName;
        Dafny.ISequence<DAST._IType> _1362_typeArgs = _source58.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _1363_args = _source58.dtor_args;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1364_maybeOutVars = _source58.dtor_outs;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          RAST._IExpr _1365_onExpr;
          DCOMP._IOwnership _1366___v67;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1367_enclosingIdents;
          RAST._IExpr _out152;
          DCOMP._IOwnership _out153;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out154;
          (this).GenExpr(_1360_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out152, out _out153, out _out154);
          _1365_onExpr = _out152;
          _1366___v67 = _out153;
          _1367_enclosingIdents = _out154;
          Dafny.ISequence<RAST._IType> _1368_typeArgsR;
          _1368_typeArgsR = Dafny.Sequence<RAST._IType>.FromElements();
          if ((new BigInteger((_1362_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _1369_typeI;
            _1369_typeI = BigInteger.Zero;
            while ((_1369_typeI) < (new BigInteger((_1362_typeArgs).Count))) {
              RAST._IType _1370_tpe;
              RAST._IType _out155;
              _out155 = (this).GenType((_1362_typeArgs).Select(_1369_typeI), false, false);
              _1370_tpe = _out155;
              _1368_typeArgsR = Dafny.Sequence<RAST._IType>.Concat(_1368_typeArgsR, Dafny.Sequence<RAST._IType>.FromElements(_1370_tpe));
              _1369_typeI = (_1369_typeI) + (BigInteger.One);
            }
          }
          Dafny.ISequence<RAST._IExpr> _1371_argExprs;
          _1371_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi28 = new BigInteger((_1363_args).Count);
          for (BigInteger _1372_i = BigInteger.Zero; _1372_i < _hi28; _1372_i++) {
            DCOMP._IOwnership _1373_argOwnership;
            _1373_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            if (((_1361_name).is_CallName) && ((_1372_i) < (new BigInteger((((_1361_name).dtor_signature)).Count)))) {
              RAST._IType _1374_tpe;
              RAST._IType _out156;
              _out156 = (this).GenType(((((_1361_name).dtor_signature)).Select(_1372_i)).dtor_typ, false, false);
              _1374_tpe = _out156;
              if ((_1374_tpe).CanReadWithoutClone()) {
                _1373_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
              }
            }
            RAST._IExpr _1375_argExpr;
            DCOMP._IOwnership _1376_ownership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1377_argIdents;
            RAST._IExpr _out157;
            DCOMP._IOwnership _out158;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out159;
            (this).GenExpr((_1363_args).Select(_1372_i), selfIdent, env, _1373_argOwnership, out _out157, out _out158, out _out159);
            _1375_argExpr = _out157;
            _1376_ownership = _out158;
            _1377_argIdents = _out159;
            _1371_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1371_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1375_argExpr));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1377_argIdents);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1367_enclosingIdents);
          Dafny.ISequence<Dafny.Rune> _1378_renderedName;
          DAST._ICallName _source60 = _1361_name;
          if (_source60.is_CallName) {
            Dafny.ISequence<Dafny.Rune> _1379_name = _source60.dtor_name;
            _1378_renderedName = DCOMP.__default.escapeName(_1379_name);
            goto after_match17;
          }
          bool disjunctiveMatch9 = false;
          if (_source60.is_MapBuilderAdd) {
            disjunctiveMatch9 = true;
          }
          if (_source60.is_SetBuilderAdd) {
            disjunctiveMatch9 = true;
          }
          if (disjunctiveMatch9) {
            _1378_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            goto after_match17;
          }
          _1378_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
        after_match17: ;
          DAST._IExpression _source61 = _1360_on;
          if (_source61.is_Companion) {
            {
              _1365_onExpr = (_1365_onExpr).MSel(_1378_renderedName);
            }
            goto after_match18;
          }
          {
            _1365_onExpr = (_1365_onExpr).Sel(_1378_renderedName);
          }
        after_match18: ;
          generated = _1365_onExpr;
          if ((new BigInteger((_1368_typeArgsR).Count)).Sign == 1) {
            generated = (generated).ApplyType(_1368_typeArgsR);
          }
          generated = (generated).Apply(_1371_argExprs);
          if (((_1364_maybeOutVars).is_Some) && ((new BigInteger(((_1364_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
            Dafny.ISequence<Dafny.Rune> _1380_outVar;
            _1380_outVar = DCOMP.__default.escapeName((((_1364_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
            generated = RAST.__default.AssignVar(_1380_outVar, generated);
          } else if (((_1364_maybeOutVars).is_None) || ((new BigInteger(((_1364_maybeOutVars).dtor_value).Count)).Sign == 0)) {
          } else {
            Dafny.ISequence<Dafny.Rune> _1381_tmpVar;
            _1381_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
            RAST._IExpr _1382_tmpId;
            _1382_tmpId = RAST.Expr.create_Identifier(_1381_tmpVar);
            generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1381_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1383_outVars;
            _1383_outVars = (_1364_maybeOutVars).dtor_value;
            BigInteger _hi29 = new BigInteger((_1383_outVars).Count);
            for (BigInteger _1384_outI = BigInteger.Zero; _1384_outI < _hi29; _1384_outI++) {
              Dafny.ISequence<Dafny.Rune> _1385_outVar;
              _1385_outVar = DCOMP.__default.escapeName(((_1383_outVars).Select(_1384_outI)));
              RAST._IExpr _1386_rhs;
              _1386_rhs = (_1382_tmpId).Sel(Std.Strings.__default.OfNat(_1384_outI));
              generated = (generated).Then(RAST.__default.AssignVar(_1385_outVar, _1386_rhs));
            }
          }
          newEnv = env;
        }
        goto after_match15;
      }
      if (_source58.is_Return) {
        DAST._IExpression _1387_exprDafny = _source58.dtor_expr;
        {
          RAST._IExpr _1388_expr;
          DCOMP._IOwnership _1389___v72;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1390_recIdents;
          RAST._IExpr _out160;
          DCOMP._IOwnership _out161;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out162;
          (this).GenExpr(_1387_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out160, out _out161, out _out162);
          _1388_expr = _out160;
          _1389___v72 = _out161;
          _1390_recIdents = _out162;
          readIdents = _1390_recIdents;
          if (isLast) {
            generated = _1388_expr;
          } else {
            generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1388_expr));
          }
          newEnv = env;
        }
        goto after_match15;
      }
      if (_source58.is_EarlyReturn) {
        {
          generated = earlyReturn;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
        goto after_match15;
      }
      if (_source58.is_Halt) {
        {
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
        goto after_match15;
      }
      DAST._IExpression _1391_e = _source58.dtor_Print_a0;
      {
        RAST._IExpr _1392_printedExpr;
        DCOMP._IOwnership _1393_recOwnership;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1394_recIdents;
        RAST._IExpr _out163;
        DCOMP._IOwnership _out164;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out165;
        (this).GenExpr(_1391_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out163, out _out164, out _out165);
        _1392_printedExpr = _out163;
        _1393_recOwnership = _out164;
        _1394_recIdents = _out165;
        generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1392_printedExpr)));
        readIdents = _1394_recIdents;
        newEnv = env;
      }
    after_match15: ;
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source62 = range;
      if (_source62.is_NoRange) {
        return Std.Wrappers.Option<RAST._IType>.create_None();
      }
      if (_source62.is_U8) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
      }
      if (_source62.is_U16) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
      }
      if (_source62.is_U32) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
      }
      if (_source62.is_U64) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
      }
      if (_source62.is_U128) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
      }
      if (_source62.is_I8) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
      }
      if (_source62.is_I16) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
      }
      if (_source62.is_I32) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
      }
      if (_source62.is_I64) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
      }
      if (_source62.is_I128) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
      }
      return Std.Wrappers.Option<RAST._IType>.create_None();
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
      if (_source63.is_Literal) {
        DAST._ILiteral _h140 = _source63.dtor_Literal_a0;
        if (_h140.is_BoolLiteral) {
          bool _1395_b = _h140.dtor_BoolLiteral_a0;
          {
            RAST._IExpr _out170;
            DCOMP._IOwnership _out171;
            DCOMP.COMP.FromOwned(RAST.Expr.create_LiteralBool(_1395_b), expectedOwnership, out _out170, out _out171);
            r = _out170;
            resultingOwnership = _out171;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match19;
        }
      }
      if (_source63.is_Literal) {
        DAST._ILiteral _h141 = _source63.dtor_Literal_a0;
        if (_h141.is_IntLiteral) {
          Dafny.ISequence<Dafny.Rune> _1396_i = _h141.dtor_IntLiteral_a0;
          DAST._IType _1397_t = _h141.dtor_IntLiteral_a1;
          {
            DAST._IType _source64 = _1397_t;
            if (_source64.is_Primitive) {
              DAST._IPrimitive _h80 = _source64.dtor_Primitive_a0;
              if (_h80.is_Int) {
                {
                  if ((new BigInteger((_1396_i).Count)) <= (new BigInteger(4))) {
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1396_i));
                  } else {
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1396_i, true, false));
                  }
                }
                goto after_match20;
              }
            }
            DAST._IType _1398_o = _source64;
            {
              RAST._IType _1399_genType;
              RAST._IType _out172;
              _out172 = (this).GenType(_1398_o, false, false);
              _1399_genType = _out172;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1396_i), _1399_genType);
            }
          after_match20: ;
            RAST._IExpr _out173;
            DCOMP._IOwnership _out174;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out173, out _out174);
            r = _out173;
            resultingOwnership = _out174;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match19;
        }
      }
      if (_source63.is_Literal) {
        DAST._ILiteral _h142 = _source63.dtor_Literal_a0;
        if (_h142.is_DecLiteral) {
          Dafny.ISequence<Dafny.Rune> _1400_n = _h142.dtor_DecLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _1401_d = _h142.dtor_DecLiteral_a1;
          DAST._IType _1402_t = _h142.dtor_DecLiteral_a2;
          {
            DAST._IType _source65 = _1402_t;
            if (_source65.is_Primitive) {
              DAST._IPrimitive _h81 = _source65.dtor_Primitive_a0;
              if (_h81.is_Real) {
                {
                  r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1400_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1401_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                }
                goto after_match21;
              }
            }
            DAST._IType _1403_o = _source65;
            {
              RAST._IType _1404_genType;
              RAST._IType _out175;
              _out175 = (this).GenType(_1403_o, false, false);
              _1404_genType = _out175;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1400_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1401_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1404_genType);
            }
          after_match21: ;
            RAST._IExpr _out176;
            DCOMP._IOwnership _out177;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out176, out _out177);
            r = _out176;
            resultingOwnership = _out177;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match19;
        }
      }
      if (_source63.is_Literal) {
        DAST._ILiteral _h143 = _source63.dtor_Literal_a0;
        if (_h143.is_StringLiteral) {
          Dafny.ISequence<Dafny.Rune> _1405_l = _h143.dtor_StringLiteral_a0;
          bool _1406_verbatim = _h143.dtor_verbatim;
          {
            if (_1406_verbatim) {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Verbatim strings prefixed by @ not supported yet."));
            }
            r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1405_l, false, _1406_verbatim));
            RAST._IExpr _out178;
            DCOMP._IOwnership _out179;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out178, out _out179);
            r = _out178;
            resultingOwnership = _out179;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match19;
        }
      }
      if (_source63.is_Literal) {
        DAST._ILiteral _h144 = _source63.dtor_Literal_a0;
        if (_h144.is_CharLiteralUTF16) {
          BigInteger _1407_c = _h144.dtor_CharLiteralUTF16_a0;
          {
            r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1407_c));
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
          goto after_match19;
        }
      }
      if (_source63.is_Literal) {
        DAST._ILiteral _h145 = _source63.dtor_Literal_a0;
        if (_h145.is_CharLiteral) {
          Dafny.Rune _1408_c = _h145.dtor_CharLiteral_a0;
          {
            r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1408_c).Value)));
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
          goto after_match19;
        }
      }
      DAST._ILiteral _h146 = _source63.dtor_Literal_a0;
      DAST._IType _1409_tpe = _h146.dtor_Null_a0;
      {
        RAST._IType _1410_tpeGen;
        RAST._IType _out184;
        _out184 = (this).GenType(_1409_tpe, false, false);
        _1410_tpeGen = _out184;
        r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None")), _1410_tpeGen);
        RAST._IExpr _out185;
        DCOMP._IOwnership _out186;
        DCOMP.COMP.FromOwned(r, expectedOwnership, out _out185, out _out186);
        r = _out185;
        resultingOwnership = _out186;
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        return ;
      }
    after_match19: ;
    }
    public void GenExprBinary(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs52 = e;
      DAST._IBinOp _1411_op = _let_tmp_rhs52.dtor_op;
      DAST._IExpression _1412_lExpr = _let_tmp_rhs52.dtor_left;
      DAST._IExpression _1413_rExpr = _let_tmp_rhs52.dtor_right;
      DAST.Format._IBinaryOpFormat _1414_format = _let_tmp_rhs52.dtor_format2;
      bool _1415_becomesLeftCallsRight;
      DAST._IBinOp _source66 = _1411_op;
      bool disjunctiveMatch10 = false;
      if (_source66.is_SetMerge) {
        disjunctiveMatch10 = true;
      }
      if (_source66.is_SetSubtraction) {
        disjunctiveMatch10 = true;
      }
      if (_source66.is_SetIntersection) {
        disjunctiveMatch10 = true;
      }
      if (_source66.is_SetDisjoint) {
        disjunctiveMatch10 = true;
      }
      if (_source66.is_MapMerge) {
        disjunctiveMatch10 = true;
      }
      if (_source66.is_MapSubtraction) {
        disjunctiveMatch10 = true;
      }
      if (_source66.is_MultisetMerge) {
        disjunctiveMatch10 = true;
      }
      if (_source66.is_MultisetSubtraction) {
        disjunctiveMatch10 = true;
      }
      if (_source66.is_MultisetIntersection) {
        disjunctiveMatch10 = true;
      }
      if (_source66.is_MultisetDisjoint) {
        disjunctiveMatch10 = true;
      }
      if (_source66.is_Concat) {
        disjunctiveMatch10 = true;
      }
      if (disjunctiveMatch10) {
        _1415_becomesLeftCallsRight = true;
        goto after_match22;
      }
      _1415_becomesLeftCallsRight = false;
    after_match22: ;
      bool _1416_becomesRightCallsLeft;
      DAST._IBinOp _source67 = _1411_op;
      if (_source67.is_In) {
        _1416_becomesRightCallsLeft = true;
        goto after_match23;
      }
      _1416_becomesRightCallsLeft = false;
    after_match23: ;
      bool _1417_becomesCallLeftRight;
      DAST._IBinOp _source68 = _1411_op;
      if (_source68.is_Eq) {
        bool referential0 = _source68.dtor_referential;
        if ((referential0) == (true)) {
          bool nullable0 = _source68.dtor_nullable;
          if ((nullable0) == (false)) {
            _1417_becomesCallLeftRight = true;
            goto after_match24;
          }
        }
      }
      if (_source68.is_SetMerge) {
        _1417_becomesCallLeftRight = true;
        goto after_match24;
      }
      if (_source68.is_SetSubtraction) {
        _1417_becomesCallLeftRight = true;
        goto after_match24;
      }
      if (_source68.is_SetIntersection) {
        _1417_becomesCallLeftRight = true;
        goto after_match24;
      }
      if (_source68.is_SetDisjoint) {
        _1417_becomesCallLeftRight = true;
        goto after_match24;
      }
      if (_source68.is_MapMerge) {
        _1417_becomesCallLeftRight = true;
        goto after_match24;
      }
      if (_source68.is_MapSubtraction) {
        _1417_becomesCallLeftRight = true;
        goto after_match24;
      }
      if (_source68.is_MultisetMerge) {
        _1417_becomesCallLeftRight = true;
        goto after_match24;
      }
      if (_source68.is_MultisetSubtraction) {
        _1417_becomesCallLeftRight = true;
        goto after_match24;
      }
      if (_source68.is_MultisetIntersection) {
        _1417_becomesCallLeftRight = true;
        goto after_match24;
      }
      if (_source68.is_MultisetDisjoint) {
        _1417_becomesCallLeftRight = true;
        goto after_match24;
      }
      if (_source68.is_Concat) {
        _1417_becomesCallLeftRight = true;
        goto after_match24;
      }
      _1417_becomesCallLeftRight = false;
    after_match24: ;
      DCOMP._IOwnership _1418_expectedLeftOwnership;
      if (_1415_becomesLeftCallsRight) {
        _1418_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipAutoBorrowed();
      } else if ((_1416_becomesRightCallsLeft) || (_1417_becomesCallLeftRight)) {
        _1418_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        _1418_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipOwned();
      }
      DCOMP._IOwnership _1419_expectedRightOwnership;
      if ((_1415_becomesLeftCallsRight) || (_1417_becomesCallLeftRight)) {
        _1419_expectedRightOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else if (_1416_becomesRightCallsLeft) {
        _1419_expectedRightOwnership = DCOMP.Ownership.create_OwnershipAutoBorrowed();
      } else {
        _1419_expectedRightOwnership = DCOMP.Ownership.create_OwnershipOwned();
      }
      RAST._IExpr _1420_left;
      DCOMP._IOwnership _1421___v77;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1422_recIdentsL;
      RAST._IExpr _out187;
      DCOMP._IOwnership _out188;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out189;
      (this).GenExpr(_1412_lExpr, selfIdent, env, _1418_expectedLeftOwnership, out _out187, out _out188, out _out189);
      _1420_left = _out187;
      _1421___v77 = _out188;
      _1422_recIdentsL = _out189;
      RAST._IExpr _1423_right;
      DCOMP._IOwnership _1424___v78;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1425_recIdentsR;
      RAST._IExpr _out190;
      DCOMP._IOwnership _out191;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out192;
      (this).GenExpr(_1413_rExpr, selfIdent, env, _1419_expectedRightOwnership, out _out190, out _out191, out _out192);
      _1423_right = _out190;
      _1424___v78 = _out191;
      _1425_recIdentsR = _out192;
      DAST._IBinOp _source69 = _1411_op;
      if (_source69.is_In) {
        {
          r = ((_1423_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1420_left);
        }
        goto after_match25;
      }
      if (_source69.is_SeqProperPrefix) {
        r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1420_left, _1423_right, _1414_format);
        goto after_match25;
      }
      if (_source69.is_SeqPrefix) {
        r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1420_left, _1423_right, _1414_format);
        goto after_match25;
      }
      if (_source69.is_SetMerge) {
        {
          r = ((_1420_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1423_right);
        }
        goto after_match25;
      }
      if (_source69.is_SetSubtraction) {
        {
          r = ((_1420_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1423_right);
        }
        goto after_match25;
      }
      if (_source69.is_SetIntersection) {
        {
          r = ((_1420_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1423_right);
        }
        goto after_match25;
      }
      if (_source69.is_Subset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1420_left, _1423_right, _1414_format);
        }
        goto after_match25;
      }
      if (_source69.is_ProperSubset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1420_left, _1423_right, _1414_format);
        }
        goto after_match25;
      }
      if (_source69.is_SetDisjoint) {
        {
          r = ((_1420_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1423_right);
        }
        goto after_match25;
      }
      if (_source69.is_MapMerge) {
        {
          r = ((_1420_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1423_right);
        }
        goto after_match25;
      }
      if (_source69.is_MapSubtraction) {
        {
          r = ((_1420_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1423_right);
        }
        goto after_match25;
      }
      if (_source69.is_MultisetMerge) {
        {
          r = ((_1420_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1423_right);
        }
        goto after_match25;
      }
      if (_source69.is_MultisetSubtraction) {
        {
          r = ((_1420_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1423_right);
        }
        goto after_match25;
      }
      if (_source69.is_MultisetIntersection) {
        {
          r = ((_1420_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1423_right);
        }
        goto after_match25;
      }
      if (_source69.is_Submultiset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1420_left, _1423_right, _1414_format);
        }
        goto after_match25;
      }
      if (_source69.is_ProperSubmultiset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1420_left, _1423_right, _1414_format);
        }
        goto after_match25;
      }
      if (_source69.is_MultisetDisjoint) {
        {
          r = ((_1420_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1423_right);
        }
        goto after_match25;
      }
      if (_source69.is_Concat) {
        {
          r = ((_1420_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1423_right);
        }
        goto after_match25;
      }
      {
        if ((DCOMP.COMP.OpTable).Contains(_1411_op)) {
          r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1411_op), _1420_left, _1423_right, _1414_format);
        } else {
          DAST._IBinOp _source70 = _1411_op;
          if (_source70.is_Eq) {
            bool _1426_referential = _source70.dtor_referential;
            bool _1427_nullable = _source70.dtor_nullable;
            {
              if (_1426_referential) {
                if (_1427_nullable) {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1420_left, _1423_right));
                } else {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1420_left, _1423_right));
                }
              } else {
                r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1420_left, _1423_right, DAST.Format.BinaryOpFormat.create_NoFormat());
              }
            }
            goto after_match26;
          }
          if (_source70.is_EuclidianDiv) {
            {
              r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1420_left, _1423_right));
            }
            goto after_match26;
          }
          if (_source70.is_EuclidianMod) {
            {
              r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1420_left, _1423_right));
            }
            goto after_match26;
          }
          Dafny.ISequence<Dafny.Rune> _1428_op = _source70.dtor_Passthrough_a0;
          {
            r = RAST.Expr.create_BinaryOp(_1428_op, _1420_left, _1423_right, _1414_format);
          }
        after_match26: ;
        }
      }
    after_match25: ;
      RAST._IExpr _out193;
      DCOMP._IOwnership _out194;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out193, out _out194);
      r = _out193;
      resultingOwnership = _out194;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1422_recIdentsL, _1425_recIdentsR);
      return ;
    }
    public void GenExprConvertFromNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs53 = e;
      DAST._IExpression _1429_expr = _let_tmp_rhs53.dtor_value;
      DAST._IType _1430_fromTpe = _let_tmp_rhs53.dtor_from;
      DAST._IType _1431_toTpe = _let_tmp_rhs53.dtor_typ;
      RAST._IExpr _1432_recursiveGen;
      DCOMP._IOwnership _1433_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1434_recIdents;
      RAST._IExpr _out195;
      DCOMP._IOwnership _out196;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out197;
      (this).GenExpr(_1429_expr, selfIdent, env, expectedOwnership, out _out195, out _out196, out _out197);
      _1432_recursiveGen = _out195;
      _1433_recOwned = _out196;
      _1434_recIdents = _out197;
      r = _1432_recursiveGen;
      if (object.Equals(_1433_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      RAST._IExpr _out198;
      DCOMP._IOwnership _out199;
      DCOMP.COMP.FromOwnership(r, _1433_recOwned, expectedOwnership, out _out198, out _out199);
      r = _out198;
      resultingOwnership = _out199;
      readIdents = _1434_recIdents;
    }
    public void GenExprConvertToNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IExpression _1435_expr = _let_tmp_rhs54.dtor_value;
      DAST._IType _1436_fromTpe = _let_tmp_rhs54.dtor_from;
      DAST._IType _1437_toTpe = _let_tmp_rhs54.dtor_typ;
      RAST._IExpr _1438_recursiveGen;
      DCOMP._IOwnership _1439_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1440_recIdents;
      RAST._IExpr _out200;
      DCOMP._IOwnership _out201;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out202;
      (this).GenExpr(_1435_expr, selfIdent, env, expectedOwnership, out _out200, out _out201, out _out202);
      _1438_recursiveGen = _out200;
      _1439_recOwned = _out201;
      _1440_recIdents = _out202;
      r = _1438_recursiveGen;
      if (object.Equals(_1439_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
      RAST._IExpr _out203;
      DCOMP._IOwnership _out204;
      DCOMP.COMP.FromOwnership(r, _1439_recOwned, expectedOwnership, out _out203, out _out204);
      r = _out203;
      resultingOwnership = _out204;
      readIdents = _1440_recIdents;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _1441_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _1442_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _1443_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _1443_toTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1444___v80 = _let_tmp_rhs56.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _1445___v81 = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      DAST._IType _1446_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _1447_range = _let_tmp_rhs57.dtor_range;
      bool _1448_erase = _let_tmp_rhs57.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1449_attributes = _let_tmp_rhs57.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _1450_nativeToType;
      _1450_nativeToType = DCOMP.COMP.NewtypeToRustType(_1446_b, _1447_range);
      if (object.Equals(_1442_fromTpe, _1446_b)) {
        RAST._IExpr _1451_recursiveGen;
        DCOMP._IOwnership _1452_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1453_recIdents;
        RAST._IExpr _out205;
        DCOMP._IOwnership _out206;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out207;
        (this).GenExpr(_1441_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out205, out _out206, out _out207);
        _1451_recursiveGen = _out205;
        _1452_recOwned = _out206;
        _1453_recIdents = _out207;
        readIdents = _1453_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source71 = _1450_nativeToType;
        if (_source71.is_Some) {
          RAST._IType _1454_v = _source71.dtor_value;
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1451_recursiveGen, RAST.Expr.create_ExprFromType(_1454_v)));
          RAST._IExpr _out208;
          DCOMP._IOwnership _out209;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out208, out _out209);
          r = _out208;
          resultingOwnership = _out209;
          goto after_match27;
        }
        if (_1448_erase) {
          r = _1451_recursiveGen;
        } else {
          RAST._IType _1455_rhsType;
          RAST._IType _out210;
          _out210 = (this).GenType(_1443_toTpe, true, false);
          _1455_rhsType = _out210;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1455_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1451_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
        }
        RAST._IExpr _out211;
        DCOMP._IOwnership _out212;
        DCOMP.COMP.FromOwnership(r, _1452_recOwned, expectedOwnership, out _out211, out _out212);
        r = _out211;
        resultingOwnership = _out212;
      after_match27: ;
      } else {
        RAST._IExpr _out213;
        DCOMP._IOwnership _out214;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out215;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1441_expr, _1442_fromTpe, _1446_b), _1446_b, _1443_toTpe), selfIdent, env, expectedOwnership, out _out213, out _out214, out _out215);
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
      DAST._IExpression _1456_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _1457_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _1458_toTpe = _let_tmp_rhs58.dtor_typ;
      DAST._IType _let_tmp_rhs59 = _1457_fromTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1459___v82 = _let_tmp_rhs59.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _1460___v83 = _let_tmp_rhs59.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs60 = _let_tmp_rhs59.dtor_resolved;
      DAST._IType _1461_b = _let_tmp_rhs60.dtor_baseType;
      DAST._INewtypeRange _1462_range = _let_tmp_rhs60.dtor_range;
      bool _1463_erase = _let_tmp_rhs60.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1464_attributes = _let_tmp_rhs60.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _1465_nativeFromType;
      _1465_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1461_b, _1462_range);
      if (object.Equals(_1461_b, _1458_toTpe)) {
        RAST._IExpr _1466_recursiveGen;
        DCOMP._IOwnership _1467_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1468_recIdents;
        RAST._IExpr _out216;
        DCOMP._IOwnership _out217;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out218;
        (this).GenExpr(_1456_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out216, out _out217, out _out218);
        _1466_recursiveGen = _out216;
        _1467_recOwned = _out217;
        _1468_recIdents = _out218;
        readIdents = _1468_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source72 = _1465_nativeFromType;
        if (_source72.is_Some) {
          RAST._IType _1469_v = _source72.dtor_value;
          RAST._IType _1470_toTpeRust;
          RAST._IType _out219;
          _out219 = (this).GenType(_1458_toTpe, false, false);
          _1470_toTpeRust = _out219;
          r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1470_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1466_recursiveGen));
          RAST._IExpr _out220;
          DCOMP._IOwnership _out221;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out220, out _out221);
          r = _out220;
          resultingOwnership = _out221;
          goto after_match28;
        }
        if (_1463_erase) {
          r = _1466_recursiveGen;
        } else {
          r = (_1466_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
        }
        RAST._IExpr _out222;
        DCOMP._IOwnership _out223;
        DCOMP.COMP.FromOwnership(r, _1467_recOwned, expectedOwnership, out _out222, out _out223);
        r = _out222;
        resultingOwnership = _out223;
      after_match28: ;
      } else {
        if ((_1465_nativeFromType).is_Some) {
          if (object.Equals(_1458_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1471_recursiveGen;
            DCOMP._IOwnership _1472_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1473_recIdents;
            RAST._IExpr _out224;
            DCOMP._IOwnership _out225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out226;
            (this).GenExpr(_1456_expr, selfIdent, env, expectedOwnership, out _out224, out _out225, out _out226);
            _1471_recursiveGen = _out224;
            _1472_recOwned = _out225;
            _1473_recIdents = _out226;
            RAST._IExpr _out227;
            DCOMP._IOwnership _out228;
            DCOMP.COMP.FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1471_recursiveGen, (this).DafnyCharUnderlying)), _1472_recOwned, expectedOwnership, out _out227, out _out228);
            r = _out227;
            resultingOwnership = _out228;
            readIdents = _1473_recIdents;
            return ;
          }
        }
        RAST._IExpr _out229;
        DCOMP._IOwnership _out230;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out231;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1456_expr, _1457_fromTpe, _1461_b), _1461_b, _1458_toTpe), selfIdent, env, expectedOwnership, out _out229, out _out230, out _out231);
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
      DAST._IExpression _1474_expr = _let_tmp_rhs61.dtor_value;
      DAST._IType _1475_fromTpe = _let_tmp_rhs61.dtor_from;
      DAST._IType _1476_toTpe = _let_tmp_rhs61.dtor_typ;
      RAST._IType _1477_fromTpeGen;
      RAST._IType _out232;
      _out232 = (this).GenType(_1475_fromTpe, true, false);
      _1477_fromTpeGen = _out232;
      RAST._IType _1478_toTpeGen;
      RAST._IType _out233;
      _out233 = (this).GenType(_1476_toTpe, true, false);
      _1478_toTpeGen = _out233;
      RAST._IExpr _1479_recursiveGen;
      DCOMP._IOwnership _1480_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1481_recIdents;
      RAST._IExpr _out234;
      DCOMP._IOwnership _out235;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out236;
      (this).GenExpr(_1474_expr, selfIdent, env, expectedOwnership, out _out234, out _out235, out _out236);
      _1479_recursiveGen = _out234;
      _1480_recOwned = _out235;
      _1481_recIdents = _out236;
      Dafny.ISequence<Dafny.Rune> _1482_msg;
      _1482_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1477_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1478_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1482_msg);
      r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1479_recursiveGen)._ToString(DCOMP.__default.IND), _1482_msg));
      RAST._IExpr _out237;
      DCOMP._IOwnership _out238;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out237, out _out238);
      r = _out237;
      resultingOwnership = _out238;
      readIdents = _1481_recIdents;
    }
    public void GenExprConvert(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs62 = e;
      DAST._IExpression _1483_expr = _let_tmp_rhs62.dtor_value;
      DAST._IType _1484_fromTpe = _let_tmp_rhs62.dtor_from;
      DAST._IType _1485_toTpe = _let_tmp_rhs62.dtor_typ;
      if (object.Equals(_1484_fromTpe, _1485_toTpe)) {
        RAST._IExpr _1486_recursiveGen;
        DCOMP._IOwnership _1487_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1488_recIdents;
        RAST._IExpr _out239;
        DCOMP._IOwnership _out240;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out241;
        (this).GenExpr(_1483_expr, selfIdent, env, expectedOwnership, out _out239, out _out240, out _out241);
        _1486_recursiveGen = _out239;
        _1487_recOwned = _out240;
        _1488_recIdents = _out241;
        r = _1486_recursiveGen;
        RAST._IExpr _out242;
        DCOMP._IOwnership _out243;
        DCOMP.COMP.FromOwnership(r, _1487_recOwned, expectedOwnership, out _out242, out _out243);
        r = _out242;
        resultingOwnership = _out243;
        readIdents = _1488_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source73 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1484_fromTpe, _1485_toTpe);
        DAST._IType _01 = _source73.dtor__0;
        if (_01.is_Nullable) {
          {
            RAST._IExpr _out244;
            DCOMP._IOwnership _out245;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out246;
            (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out244, out _out245, out _out246);
            r = _out244;
            resultingOwnership = _out245;
            readIdents = _out246;
          }
          goto after_match29;
        }
        DAST._IType _11 = _source73.dtor__1;
        if (_11.is_Nullable) {
          {
            RAST._IExpr _out247;
            DCOMP._IOwnership _out248;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out249;
            (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out247, out _out248, out _out249);
            r = _out247;
            resultingOwnership = _out248;
            readIdents = _out249;
          }
          goto after_match29;
        }
        DAST._IType _12 = _source73.dtor__1;
        if (_12.is_Path) {
          DAST._IResolvedType resolved1 = _12.dtor_resolved;
          if (resolved1.is_Newtype) {
            DAST._IType _1489_b = resolved1.dtor_baseType;
            DAST._INewtypeRange _1490_range = resolved1.dtor_range;
            bool _1491_erase = resolved1.dtor_erase;
            Dafny.ISequence<DAST._IAttribute> _1492_attributes = resolved1.dtor_attributes;
            {
              RAST._IExpr _out250;
              DCOMP._IOwnership _out251;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out252;
              (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out250, out _out251, out _out252);
              r = _out250;
              resultingOwnership = _out251;
              readIdents = _out252;
            }
            goto after_match29;
          }
        }
        DAST._IType _02 = _source73.dtor__0;
        if (_02.is_Path) {
          DAST._IResolvedType resolved2 = _02.dtor_resolved;
          if (resolved2.is_Newtype) {
            DAST._IType _1493_b = resolved2.dtor_baseType;
            DAST._INewtypeRange _1494_range = resolved2.dtor_range;
            bool _1495_erase = resolved2.dtor_erase;
            Dafny.ISequence<DAST._IAttribute> _1496_attributes = resolved2.dtor_attributes;
            {
              RAST._IExpr _out253;
              DCOMP._IOwnership _out254;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out255;
              (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out253, out _out254, out _out255);
              r = _out253;
              resultingOwnership = _out254;
              readIdents = _out255;
            }
            goto after_match29;
          }
        }
        DAST._IType _03 = _source73.dtor__0;
        if (_03.is_Primitive) {
          DAST._IPrimitive _h82 = _03.dtor_Primitive_a0;
          if (_h82.is_Int) {
            DAST._IType _13 = _source73.dtor__1;
            if (_13.is_Primitive) {
              DAST._IPrimitive _h83 = _13.dtor_Primitive_a0;
              if (_h83.is_Real) {
                {
                  RAST._IExpr _1497_recursiveGen;
                  DCOMP._IOwnership _1498___v94;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1499_recIdents;
                  RAST._IExpr _out256;
                  DCOMP._IOwnership _out257;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out258;
                  (this).GenExpr(_1483_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out256, out _out257, out _out258);
                  _1497_recursiveGen = _out256;
                  _1498___v94 = _out257;
                  _1499_recIdents = _out258;
                  r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1497_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                  RAST._IExpr _out259;
                  DCOMP._IOwnership _out260;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out259, out _out260);
                  r = _out259;
                  resultingOwnership = _out260;
                  readIdents = _1499_recIdents;
                }
                goto after_match29;
              }
            }
          }
        }
        DAST._IType _04 = _source73.dtor__0;
        if (_04.is_Primitive) {
          DAST._IPrimitive _h84 = _04.dtor_Primitive_a0;
          if (_h84.is_Real) {
            DAST._IType _14 = _source73.dtor__1;
            if (_14.is_Primitive) {
              DAST._IPrimitive _h85 = _14.dtor_Primitive_a0;
              if (_h85.is_Int) {
                {
                  RAST._IExpr _1500_recursiveGen;
                  DCOMP._IOwnership _1501___v95;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1502_recIdents;
                  RAST._IExpr _out261;
                  DCOMP._IOwnership _out262;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out263;
                  (this).GenExpr(_1483_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out261, out _out262, out _out263);
                  _1500_recursiveGen = _out261;
                  _1501___v95 = _out262;
                  _1502_recIdents = _out263;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1500_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                  RAST._IExpr _out264;
                  DCOMP._IOwnership _out265;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out264, out _out265);
                  r = _out264;
                  resultingOwnership = _out265;
                  readIdents = _1502_recIdents;
                }
                goto after_match29;
              }
            }
          }
        }
        DAST._IType _05 = _source73.dtor__0;
        if (_05.is_Primitive) {
          DAST._IPrimitive _h86 = _05.dtor_Primitive_a0;
          if (_h86.is_Int) {
            DAST._IType _15 = _source73.dtor__1;
            if (_15.is_Passthrough) {
              {
                RAST._IType _1503_rhsType;
                RAST._IType _out266;
                _out266 = (this).GenType(_1485_toTpe, true, false);
                _1503_rhsType = _out266;
                RAST._IExpr _1504_recursiveGen;
                DCOMP._IOwnership _1505___v97;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1506_recIdents;
                RAST._IExpr _out267;
                DCOMP._IOwnership _out268;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out269;
                (this).GenExpr(_1483_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out267, out _out268, out _out269);
                _1504_recursiveGen = _out267;
                _1505___v97 = _out268;
                _1506_recIdents = _out269;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1503_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1504_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                RAST._IExpr _out270;
                DCOMP._IOwnership _out271;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out270, out _out271);
                r = _out270;
                resultingOwnership = _out271;
                readIdents = _1506_recIdents;
              }
              goto after_match29;
            }
          }
        }
        DAST._IType _06 = _source73.dtor__0;
        if (_06.is_Passthrough) {
          DAST._IType _16 = _source73.dtor__1;
          if (_16.is_Primitive) {
            DAST._IPrimitive _h87 = _16.dtor_Primitive_a0;
            if (_h87.is_Int) {
              {
                RAST._IType _1507_rhsType;
                RAST._IType _out272;
                _out272 = (this).GenType(_1484_fromTpe, true, false);
                _1507_rhsType = _out272;
                RAST._IExpr _1508_recursiveGen;
                DCOMP._IOwnership _1509___v99;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1510_recIdents;
                RAST._IExpr _out273;
                DCOMP._IOwnership _out274;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out275;
                (this).GenExpr(_1483_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out273, out _out274, out _out275);
                _1508_recursiveGen = _out273;
                _1509___v99 = _out274;
                _1510_recIdents = _out275;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::dafny_runtime::BigInt::from("), (_1508_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")}")));
                RAST._IExpr _out276;
                DCOMP._IOwnership _out277;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out276, out _out277);
                r = _out276;
                resultingOwnership = _out277;
                readIdents = _1510_recIdents;
              }
              goto after_match29;
            }
          }
        }
        DAST._IType _07 = _source73.dtor__0;
        if (_07.is_Primitive) {
          DAST._IPrimitive _h88 = _07.dtor_Primitive_a0;
          if (_h88.is_Int) {
            DAST._IType _17 = _source73.dtor__1;
            if (_17.is_Primitive) {
              DAST._IPrimitive _h89 = _17.dtor_Primitive_a0;
              if (_h89.is_Char) {
                {
                  RAST._IType _1511_rhsType;
                  RAST._IType _out278;
                  _out278 = (this).GenType(_1485_toTpe, true, false);
                  _1511_rhsType = _out278;
                  RAST._IExpr _1512_recursiveGen;
                  DCOMP._IOwnership _1513___v100;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1514_recIdents;
                  RAST._IExpr _out279;
                  DCOMP._IOwnership _out280;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out281;
                  (this).GenExpr(_1483_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out279, out _out280, out _out281);
                  _1512_recursiveGen = _out279;
                  _1513___v100 = _out280;
                  _1514_recIdents = _out281;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), (_1512_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()")));
                  RAST._IExpr _out282;
                  DCOMP._IOwnership _out283;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out282, out _out283);
                  r = _out282;
                  resultingOwnership = _out283;
                  readIdents = _1514_recIdents;
                }
                goto after_match29;
              }
            }
          }
        }
        DAST._IType _08 = _source73.dtor__0;
        if (_08.is_Primitive) {
          DAST._IPrimitive _h810 = _08.dtor_Primitive_a0;
          if (_h810.is_Char) {
            DAST._IType _18 = _source73.dtor__1;
            if (_18.is_Primitive) {
              DAST._IPrimitive _h811 = _18.dtor_Primitive_a0;
              if (_h811.is_Int) {
                {
                  RAST._IType _1515_rhsType;
                  RAST._IType _out284;
                  _out284 = (this).GenType(_1484_fromTpe, true, false);
                  _1515_rhsType = _out284;
                  RAST._IExpr _1516_recursiveGen;
                  DCOMP._IOwnership _1517___v101;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1518_recIdents;
                  RAST._IExpr _out285;
                  DCOMP._IOwnership _out286;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out287;
                  (this).GenExpr(_1483_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out285, out _out286, out _out287);
                  _1516_recursiveGen = _out285;
                  _1517___v101 = _out286;
                  _1518_recIdents = _out287;
                  r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1516_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                  RAST._IExpr _out288;
                  DCOMP._IOwnership _out289;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out288, out _out289);
                  r = _out288;
                  resultingOwnership = _out289;
                  readIdents = _1518_recIdents;
                }
                goto after_match29;
              }
            }
          }
        }
        DAST._IType _09 = _source73.dtor__0;
        if (_09.is_Passthrough) {
          DAST._IType _19 = _source73.dtor__1;
          if (_19.is_Passthrough) {
            {
              RAST._IExpr _1519_recursiveGen;
              DCOMP._IOwnership _1520___v104;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1521_recIdents;
              RAST._IExpr _out290;
              DCOMP._IOwnership _out291;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out292;
              (this).GenExpr(_1483_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out290, out _out291, out _out292);
              _1519_recursiveGen = _out290;
              _1520___v104 = _out291;
              _1521_recIdents = _out292;
              RAST._IType _1522_toTpeGen;
              RAST._IType _out293;
              _out293 = (this).GenType(_1485_toTpe, true, false);
              _1522_toTpeGen = _out293;
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1519_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1522_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
              RAST._IExpr _out294;
              DCOMP._IOwnership _out295;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out294, out _out295);
              r = _out294;
              resultingOwnership = _out295;
              readIdents = _1521_recIdents;
            }
            goto after_match29;
          }
        }
        {
          RAST._IExpr _out296;
          DCOMP._IOwnership _out297;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out298;
          (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out296, out _out297, out _out298);
          r = _out296;
          resultingOwnership = _out297;
          readIdents = _out298;
        }
      after_match29: ;
      }
      return ;
    }
    public void GenIdent(Dafny.ISequence<Dafny.Rune> rName, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      r = RAST.Expr.create_Identifier(rName);
      Std.Wrappers._IOption<RAST._IType> _1523_tpe;
      _1523_tpe = (env).GetType(rName);
      bool _1524_currentlyBorrowed;
      _1524_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1525_noNeedOfClone;
      _1525_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        r = RAST.__default.BorrowMut(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        if (!(_1525_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1525_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1524_currentlyBorrowed) {
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
      if (_source74.is_Literal) {
        RAST._IExpr _out299;
        DCOMP._IOwnership _out300;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out301;
        (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out299, out _out300, out _out301);
        r = _out299;
        resultingOwnership = _out300;
        readIdents = _out301;
        goto after_match30;
      }
      if (_source74.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _1526_name = _source74.dtor_Ident_a0;
        {
          RAST._IExpr _out302;
          DCOMP._IOwnership _out303;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out304;
          (this).GenIdent(DCOMP.__default.escapeName(_1526_name), selfIdent, env, expectedOwnership, out _out302, out _out303, out _out304);
          r = _out302;
          resultingOwnership = _out303;
          readIdents = _out304;
        }
        goto after_match30;
      }
      if (_source74.is_Companion) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1527_path = _source74.dtor_Companion_a0;
        {
          RAST._IExpr _out305;
          _out305 = DCOMP.COMP.GenPathExpr(_1527_path);
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
        goto after_match30;
      }
      if (_source74.is_InitializationValue) {
        DAST._IType _1528_typ = _source74.dtor_typ;
        {
          RAST._IType _1529_typExpr;
          RAST._IType _out308;
          _out308 = (this).GenType(_1528_typ, false, false);
          _1529_typExpr = _out308;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1529_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
          RAST._IExpr _out309;
          DCOMP._IOwnership _out310;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out309, out _out310);
          r = _out309;
          resultingOwnership = _out310;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_Tuple) {
        Dafny.ISequence<DAST._IExpression> _1530_values = _source74.dtor_Tuple_a0;
        {
          Dafny.ISequence<RAST._IExpr> _1531_exprs;
          _1531_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _hi30 = new BigInteger((_1530_values).Count);
          for (BigInteger _1532_i = BigInteger.Zero; _1532_i < _hi30; _1532_i++) {
            RAST._IExpr _1533_recursiveGen;
            DCOMP._IOwnership _1534___v107;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1535_recIdents;
            RAST._IExpr _out311;
            DCOMP._IOwnership _out312;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out313;
            (this).GenExpr((_1530_values).Select(_1532_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out311, out _out312, out _out313);
            _1533_recursiveGen = _out311;
            _1534___v107 = _out312;
            _1535_recIdents = _out313;
            _1531_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1531_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1533_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1535_recIdents);
          }
          if ((new BigInteger((_1530_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) {
            r = RAST.Expr.create_Tuple(_1531_exprs);
          } else {
            r = RAST.__default.SystemTuple(_1531_exprs);
          }
          RAST._IExpr _out314;
          DCOMP._IOwnership _out315;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out314, out _out315);
          r = _out314;
          resultingOwnership = _out315;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_New) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1536_path = _source74.dtor_path;
        Dafny.ISequence<DAST._IType> _1537_typeArgs = _source74.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _1538_args = _source74.dtor_args;
        {
          RAST._IExpr _out316;
          _out316 = DCOMP.COMP.GenPathExpr(_1536_path);
          r = _out316;
          if ((new BigInteger((_1537_typeArgs).Count)).Sign == 1) {
            Dafny.ISequence<RAST._IType> _1539_typeExprs;
            _1539_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi31 = new BigInteger((_1537_typeArgs).Count);
            for (BigInteger _1540_i = BigInteger.Zero; _1540_i < _hi31; _1540_i++) {
              RAST._IType _1541_typeExpr;
              RAST._IType _out317;
              _out317 = (this).GenType((_1537_typeArgs).Select(_1540_i), false, false);
              _1541_typeExpr = _out317;
              _1539_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1539_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1541_typeExpr));
            }
            r = (r).ApplyType(_1539_typeExprs);
          }
          r = (r).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<RAST._IExpr> _1542_arguments;
          _1542_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi32 = new BigInteger((_1538_args).Count);
          for (BigInteger _1543_i = BigInteger.Zero; _1543_i < _hi32; _1543_i++) {
            RAST._IExpr _1544_recursiveGen;
            DCOMP._IOwnership _1545___v108;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1546_recIdents;
            RAST._IExpr _out318;
            DCOMP._IOwnership _out319;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out320;
            (this).GenExpr((_1538_args).Select(_1543_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out318, out _out319, out _out320);
            _1544_recursiveGen = _out318;
            _1545___v108 = _out319;
            _1546_recIdents = _out320;
            _1542_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1542_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1544_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1546_recIdents);
          }
          r = (r).Apply(_1542_arguments);
          RAST._IExpr _out321;
          DCOMP._IOwnership _out322;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out321, out _out322);
          r = _out321;
          resultingOwnership = _out322;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_NewArray) {
        Dafny.ISequence<DAST._IExpression> _1547_dims = _source74.dtor_dims;
        DAST._IType _1548_typ = _source74.dtor_typ;
        {
          BigInteger _1549_i;
          _1549_i = (new BigInteger((_1547_dims).Count)) - (BigInteger.One);
          RAST._IType _1550_genTyp;
          RAST._IType _out323;
          _out323 = (this).GenType(_1548_typ, false, false);
          _1550_genTyp = _out323;
          Dafny.ISequence<Dafny.Rune> _1551_s;
          _1551_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1550_genTyp)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::std::default::Default>::default()"));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          while ((_1549_i).Sign != -1) {
            RAST._IExpr _1552_recursiveGen;
            DCOMP._IOwnership _1553___v109;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1554_recIdents;
            RAST._IExpr _out324;
            DCOMP._IOwnership _out325;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out326;
            (this).GenExpr((_1547_dims).Select(_1549_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out324, out _out325, out _out326);
            _1552_recursiveGen = _out324;
            _1553___v109 = _out325;
            _1554_recIdents = _out326;
            _1551_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), _1551_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), (_1552_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1554_recIdents);
            _1549_i = (_1549_i) - (BigInteger.One);
          }
          r = RAST.Expr.create_RawExpr(_1551_s);
          RAST._IExpr _out327;
          DCOMP._IOwnership _out328;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out327, out _out328);
          r = _out327;
          resultingOwnership = _out328;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_DatatypeValue) {
        DAST._IDatatypeType _1555_datatypeType = _source74.dtor_datatypeType;
        Dafny.ISequence<DAST._IType> _1556_typeArgs = _source74.dtor_typeArgs;
        Dafny.ISequence<Dafny.Rune> _1557_variant = _source74.dtor_variant;
        bool _1558_isCo = _source74.dtor_isCo;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1559_values = _source74.dtor_contents;
        {
          RAST._IExpr _out329;
          _out329 = DCOMP.COMP.GenPathExpr((_1555_datatypeType).dtor_path);
          r = _out329;
          Dafny.ISequence<RAST._IType> _1560_genTypeArgs;
          _1560_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _hi33 = new BigInteger((_1556_typeArgs).Count);
          for (BigInteger _1561_i = BigInteger.Zero; _1561_i < _hi33; _1561_i++) {
            RAST._IType _1562_typeExpr;
            RAST._IType _out330;
            _out330 = (this).GenType((_1556_typeArgs).Select(_1561_i), false, false);
            _1562_typeExpr = _out330;
            _1560_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1560_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1562_typeExpr));
          }
          if ((new BigInteger((_1556_typeArgs).Count)).Sign == 1) {
            r = (r).ApplyType(_1560_genTypeArgs);
          }
          r = (r).MSel(DCOMP.__default.escapeName(_1557_variant));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<RAST._IAssignIdentifier> _1563_assignments;
          _1563_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
          BigInteger _hi34 = new BigInteger((_1559_values).Count);
          for (BigInteger _1564_i = BigInteger.Zero; _1564_i < _hi34; _1564_i++) {
            _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs63 = (_1559_values).Select(_1564_i);
            Dafny.ISequence<Dafny.Rune> _1565_name = _let_tmp_rhs63.dtor__0;
            DAST._IExpression _1566_value = _let_tmp_rhs63.dtor__1;
            if (_1558_isCo) {
              RAST._IExpr _1567_recursiveGen;
              DCOMP._IOwnership _1568___v110;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1569_recIdents;
              RAST._IExpr _out331;
              DCOMP._IOwnership _out332;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out333;
              (this).GenExpr(_1566_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out331, out _out332, out _out333);
              _1567_recursiveGen = _out331;
              _1568___v110 = _out332;
              _1569_recIdents = _out333;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1569_recIdents);
              Dafny.ISequence<Dafny.Rune> _1570_allReadCloned;
              _1570_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              while (!(_1569_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                Dafny.ISequence<Dafny.Rune> _1571_next;
                foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1569_recIdents).Elements) {
                  _1571_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                  if ((_1569_recIdents).Contains(_1571_next)) {
                    goto after__ASSIGN_SUCH_THAT_2;
                  }
                }
                throw new System.Exception("assign-such-that search produced no value (line 3271)");
              after__ASSIGN_SUCH_THAT_2: ;
                _1570_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1570_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1571_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1571_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                _1569_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1569_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1571_next));
              }
              Dafny.ISequence<Dafny.Rune> _1572_wasAssigned;
              _1572_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1570_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1567_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
              _1563_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1563_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1565_name, RAST.Expr.create_RawExpr(_1572_wasAssigned))));
            } else {
              RAST._IExpr _1573_recursiveGen;
              DCOMP._IOwnership _1574___v111;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1575_recIdents;
              RAST._IExpr _out334;
              DCOMP._IOwnership _out335;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out336;
              (this).GenExpr(_1566_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out334, out _out335, out _out336);
              _1573_recursiveGen = _out334;
              _1574___v111 = _out335;
              _1575_recIdents = _out336;
              _1563_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1563_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1565_name, _1573_recursiveGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1575_recIdents);
            }
          }
          r = RAST.Expr.create_StructBuild(r, _1563_assignments);
          if ((this).IsRcWrapped((_1555_datatypeType).dtor_attributes)) {
            r = RAST.__default.RcNew(r);
          }
          RAST._IExpr _out337;
          DCOMP._IOwnership _out338;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out337, out _out338);
          r = _out337;
          resultingOwnership = _out338;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_Convert) {
        {
          RAST._IExpr _out339;
          DCOMP._IOwnership _out340;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out341;
          (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out339, out _out340, out _out341);
          r = _out339;
          resultingOwnership = _out340;
          readIdents = _out341;
        }
        goto after_match30;
      }
      if (_source74.is_SeqConstruct) {
        DAST._IExpression _1576_length = _source74.dtor_length;
        DAST._IExpression _1577_expr = _source74.dtor_elem;
        {
          RAST._IExpr _1578_recursiveGen;
          DCOMP._IOwnership _1579___v115;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1580_recIdents;
          RAST._IExpr _out342;
          DCOMP._IOwnership _out343;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out344;
          (this).GenExpr(_1577_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out342, out _out343, out _out344);
          _1578_recursiveGen = _out342;
          _1579___v115 = _out343;
          _1580_recIdents = _out344;
          RAST._IExpr _1581_lengthGen;
          DCOMP._IOwnership _1582___v116;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1583_lengthIdents;
          RAST._IExpr _out345;
          DCOMP._IOwnership _out346;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out347;
          (this).GenExpr(_1576_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out345, out _out346, out _out347);
          _1581_lengthGen = _out345;
          _1582___v116 = _out346;
          _1583_lengthIdents = _out347;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1578_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1581_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1580_recIdents, _1583_lengthIdents);
          RAST._IExpr _out348;
          DCOMP._IOwnership _out349;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out348, out _out349);
          r = _out348;
          resultingOwnership = _out349;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_SeqValue) {
        Dafny.ISequence<DAST._IExpression> _1584_exprs = _source74.dtor_elements;
        DAST._IType _1585_typ = _source74.dtor_typ;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          RAST._IType _1586_genTpe;
          RAST._IType _out350;
          _out350 = (this).GenType(_1585_typ, false, false);
          _1586_genTpe = _out350;
          BigInteger _1587_i;
          _1587_i = BigInteger.Zero;
          Dafny.ISequence<RAST._IExpr> _1588_args;
          _1588_args = Dafny.Sequence<RAST._IExpr>.FromElements();
          while ((_1587_i) < (new BigInteger((_1584_exprs).Count))) {
            RAST._IExpr _1589_recursiveGen;
            DCOMP._IOwnership _1590___v117;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1591_recIdents;
            RAST._IExpr _out351;
            DCOMP._IOwnership _out352;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out353;
            (this).GenExpr((_1584_exprs).Select(_1587_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out351, out _out352, out _out353);
            _1589_recursiveGen = _out351;
            _1590___v117 = _out352;
            _1591_recIdents = _out353;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1591_recIdents);
            _1588_args = Dafny.Sequence<RAST._IExpr>.Concat(_1588_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1589_recursiveGen));
            _1587_i = (_1587_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_1588_args);
          if ((new BigInteger((_1588_args).Count)).Sign == 0) {
            r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1586_genTpe));
          }
          RAST._IExpr _out354;
          DCOMP._IOwnership _out355;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out354, out _out355);
          r = _out354;
          resultingOwnership = _out355;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_SetValue) {
        Dafny.ISequence<DAST._IExpression> _1592_exprs = _source74.dtor_elements;
        {
          Dafny.ISequence<RAST._IExpr> _1593_generatedValues;
          _1593_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _1594_i;
          _1594_i = BigInteger.Zero;
          while ((_1594_i) < (new BigInteger((_1592_exprs).Count))) {
            RAST._IExpr _1595_recursiveGen;
            DCOMP._IOwnership _1596___v118;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1597_recIdents;
            RAST._IExpr _out356;
            DCOMP._IOwnership _out357;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out358;
            (this).GenExpr((_1592_exprs).Select(_1594_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out356, out _out357, out _out358);
            _1595_recursiveGen = _out356;
            _1596___v118 = _out357;
            _1597_recIdents = _out358;
            _1593_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1593_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1595_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1597_recIdents);
            _1594_i = (_1594_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_1593_generatedValues);
          RAST._IExpr _out359;
          DCOMP._IOwnership _out360;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out359, out _out360);
          r = _out359;
          resultingOwnership = _out360;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_MultisetValue) {
        Dafny.ISequence<DAST._IExpression> _1598_exprs = _source74.dtor_elements;
        {
          Dafny.ISequence<RAST._IExpr> _1599_generatedValues;
          _1599_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _1600_i;
          _1600_i = BigInteger.Zero;
          while ((_1600_i) < (new BigInteger((_1598_exprs).Count))) {
            RAST._IExpr _1601_recursiveGen;
            DCOMP._IOwnership _1602___v119;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1603_recIdents;
            RAST._IExpr _out361;
            DCOMP._IOwnership _out362;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out363;
            (this).GenExpr((_1598_exprs).Select(_1600_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out361, out _out362, out _out363);
            _1601_recursiveGen = _out361;
            _1602___v119 = _out362;
            _1603_recIdents = _out363;
            _1599_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1599_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1601_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1603_recIdents);
            _1600_i = (_1600_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_1599_generatedValues);
          RAST._IExpr _out364;
          DCOMP._IOwnership _out365;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out364, out _out365);
          r = _out364;
          resultingOwnership = _out365;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_ToMultiset) {
        DAST._IExpression _1604_expr = _source74.dtor_ToMultiset_a0;
        {
          RAST._IExpr _1605_recursiveGen;
          DCOMP._IOwnership _1606___v120;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1607_recIdents;
          RAST._IExpr _out366;
          DCOMP._IOwnership _out367;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out368;
          (this).GenExpr(_1604_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out366, out _out367, out _out368);
          _1605_recursiveGen = _out366;
          _1606___v120 = _out367;
          _1607_recIdents = _out368;
          r = ((_1605_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          readIdents = _1607_recIdents;
          RAST._IExpr _out369;
          DCOMP._IOwnership _out370;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out369, out _out370);
          r = _out369;
          resultingOwnership = _out370;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_MapValue) {
        Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1608_mapElems = _source74.dtor_mapElems;
        {
          Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1609_generatedValues;
          _1609_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _1610_i;
          _1610_i = BigInteger.Zero;
          while ((_1610_i) < (new BigInteger((_1608_mapElems).Count))) {
            RAST._IExpr _1611_recursiveGenKey;
            DCOMP._IOwnership _1612___v121;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1613_recIdentsKey;
            RAST._IExpr _out371;
            DCOMP._IOwnership _out372;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out373;
            (this).GenExpr(((_1608_mapElems).Select(_1610_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out371, out _out372, out _out373);
            _1611_recursiveGenKey = _out371;
            _1612___v121 = _out372;
            _1613_recIdentsKey = _out373;
            RAST._IExpr _1614_recursiveGenValue;
            DCOMP._IOwnership _1615___v122;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1616_recIdentsValue;
            RAST._IExpr _out374;
            DCOMP._IOwnership _out375;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out376;
            (this).GenExpr(((_1608_mapElems).Select(_1610_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out374, out _out375, out _out376);
            _1614_recursiveGenValue = _out374;
            _1615___v122 = _out375;
            _1616_recIdentsValue = _out376;
            _1609_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1609_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1611_recursiveGenKey, _1614_recursiveGenValue)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1613_recIdentsKey), _1616_recIdentsValue);
            _1610_i = (_1610_i) + (BigInteger.One);
          }
          _1610_i = BigInteger.Zero;
          Dafny.ISequence<RAST._IExpr> _1617_arguments;
          _1617_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          while ((_1610_i) < (new BigInteger((_1609_generatedValues).Count))) {
            RAST._IExpr _1618_genKey;
            _1618_genKey = ((_1609_generatedValues).Select(_1610_i)).dtor__0;
            RAST._IExpr _1619_genValue;
            _1619_genValue = ((_1609_generatedValues).Select(_1610_i)).dtor__1;
            _1617_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1617_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1618_genKey, _1619_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
            _1610_i = (_1610_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_1617_arguments);
          RAST._IExpr _out377;
          DCOMP._IOwnership _out378;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out377, out _out378);
          r = _out377;
          resultingOwnership = _out378;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_SeqUpdate) {
        DAST._IExpression _1620_expr = _source74.dtor_expr;
        DAST._IExpression _1621_index = _source74.dtor_indexExpr;
        DAST._IExpression _1622_value = _source74.dtor_value;
        {
          RAST._IExpr _1623_exprR;
          DCOMP._IOwnership _1624___v123;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1625_exprIdents;
          RAST._IExpr _out379;
          DCOMP._IOwnership _out380;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out381;
          (this).GenExpr(_1620_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out379, out _out380, out _out381);
          _1623_exprR = _out379;
          _1624___v123 = _out380;
          _1625_exprIdents = _out381;
          RAST._IExpr _1626_indexR;
          DCOMP._IOwnership _1627_indexOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1628_indexIdents;
          RAST._IExpr _out382;
          DCOMP._IOwnership _out383;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out384;
          (this).GenExpr(_1621_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out382, out _out383, out _out384);
          _1626_indexR = _out382;
          _1627_indexOwnership = _out383;
          _1628_indexIdents = _out384;
          RAST._IExpr _1629_valueR;
          DCOMP._IOwnership _1630_valueOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1631_valueIdents;
          RAST._IExpr _out385;
          DCOMP._IOwnership _out386;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out387;
          (this).GenExpr(_1622_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out385, out _out386, out _out387);
          _1629_valueR = _out385;
          _1630_valueOwnership = _out386;
          _1631_valueIdents = _out387;
          r = ((_1623_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1626_indexR, _1629_valueR));
          RAST._IExpr _out388;
          DCOMP._IOwnership _out389;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out388, out _out389);
          r = _out388;
          resultingOwnership = _out389;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1625_exprIdents, _1628_indexIdents), _1631_valueIdents);
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_MapUpdate) {
        DAST._IExpression _1632_expr = _source74.dtor_expr;
        DAST._IExpression _1633_index = _source74.dtor_indexExpr;
        DAST._IExpression _1634_value = _source74.dtor_value;
        {
          RAST._IExpr _1635_exprR;
          DCOMP._IOwnership _1636___v124;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1637_exprIdents;
          RAST._IExpr _out390;
          DCOMP._IOwnership _out391;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out392;
          (this).GenExpr(_1632_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out390, out _out391, out _out392);
          _1635_exprR = _out390;
          _1636___v124 = _out391;
          _1637_exprIdents = _out392;
          RAST._IExpr _1638_indexR;
          DCOMP._IOwnership _1639_indexOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1640_indexIdents;
          RAST._IExpr _out393;
          DCOMP._IOwnership _out394;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out395;
          (this).GenExpr(_1633_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out393, out _out394, out _out395);
          _1638_indexR = _out393;
          _1639_indexOwnership = _out394;
          _1640_indexIdents = _out395;
          RAST._IExpr _1641_valueR;
          DCOMP._IOwnership _1642_valueOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1643_valueIdents;
          RAST._IExpr _out396;
          DCOMP._IOwnership _out397;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out398;
          (this).GenExpr(_1634_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out396, out _out397, out _out398);
          _1641_valueR = _out396;
          _1642_valueOwnership = _out397;
          _1643_valueIdents = _out398;
          r = ((_1635_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1638_indexR, _1641_valueR));
          RAST._IExpr _out399;
          DCOMP._IOwnership _out400;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out399, out _out400);
          r = _out399;
          resultingOwnership = _out400;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1637_exprIdents, _1640_indexIdents), _1643_valueIdents);
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_This) {
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source75 = selfIdent;
          if (_source75.is_Some) {
            Dafny.ISequence<Dafny.Rune> _1644_id = _source75.dtor_value;
            {
              r = RAST.Expr.create_Identifier(_1644_id);
              if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
                r = RAST.__default.Clone(r);
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
                r = RAST.__default.BoxNew(RAST.__default.Clone(r));
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
              } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
                if (!(_1644_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  r = RAST.__default.Borrow(r);
                }
                resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              } else {
                if (!(_1644_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  r = RAST.__default.BorrowMut(r);
                }
                resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
              }
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1644_id);
            }
            goto after_match31;
          }
          {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")"));
            RAST._IExpr _out401;
            DCOMP._IOwnership _out402;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out401, out _out402);
            r = _out401;
            resultingOwnership = _out402;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        after_match31: ;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_Ite) {
        DAST._IExpression _1645_cond = _source74.dtor_cond;
        DAST._IExpression _1646_t = _source74.dtor_thn;
        DAST._IExpression _1647_f = _source74.dtor_els;
        {
          RAST._IExpr _1648_cond;
          DCOMP._IOwnership _1649___v125;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1650_recIdentsCond;
          RAST._IExpr _out403;
          DCOMP._IOwnership _out404;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out405;
          (this).GenExpr(_1645_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out403, out _out404, out _out405);
          _1648_cond = _out403;
          _1649___v125 = _out404;
          _1650_recIdentsCond = _out405;
          Dafny.ISequence<Dafny.Rune> _1651_condString;
          _1651_condString = (_1648_cond)._ToString(DCOMP.__default.IND);
          RAST._IExpr _1652___v126;
          DCOMP._IOwnership _1653_tHasToBeOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1654___v127;
          RAST._IExpr _out406;
          DCOMP._IOwnership _out407;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out408;
          (this).GenExpr(_1646_t, selfIdent, env, expectedOwnership, out _out406, out _out407, out _out408);
          _1652___v126 = _out406;
          _1653_tHasToBeOwned = _out407;
          _1654___v127 = _out408;
          RAST._IExpr _1655_fExpr;
          DCOMP._IOwnership _1656_fOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1657_recIdentsF;
          RAST._IExpr _out409;
          DCOMP._IOwnership _out410;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out411;
          (this).GenExpr(_1647_f, selfIdent, env, _1653_tHasToBeOwned, out _out409, out _out410, out _out411);
          _1655_fExpr = _out409;
          _1656_fOwned = _out410;
          _1657_recIdentsF = _out411;
          Dafny.ISequence<Dafny.Rune> _1658_fString;
          _1658_fString = (_1655_fExpr)._ToString(DCOMP.__default.IND);
          RAST._IExpr _1659_tExpr;
          DCOMP._IOwnership _1660___v128;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1661_recIdentsT;
          RAST._IExpr _out412;
          DCOMP._IOwnership _out413;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out414;
          (this).GenExpr(_1646_t, selfIdent, env, _1656_fOwned, out _out412, out _out413, out _out414);
          _1659_tExpr = _out412;
          _1660___v128 = _out413;
          _1661_recIdentsT = _out414;
          Dafny.ISequence<Dafny.Rune> _1662_tString;
          _1662_tString = (_1659_tExpr)._ToString(DCOMP.__default.IND);
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _1651_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _1662_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _1658_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})")));
          RAST._IExpr _out415;
          DCOMP._IOwnership _out416;
          DCOMP.COMP.FromOwnership(r, _1656_fOwned, expectedOwnership, out _out415, out _out416);
          r = _out415;
          resultingOwnership = _out416;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1650_recIdentsCond, _1661_recIdentsT), _1657_recIdentsF);
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_UnOp) {
        DAST._IUnaryOp unOp0 = _source74.dtor_unOp;
        if (unOp0.is_Not) {
          DAST._IExpression _1663_e = _source74.dtor_expr;
          DAST.Format._IUnaryOpFormat _1664_format = _source74.dtor_format1;
          {
            RAST._IExpr _1665_recursiveGen;
            DCOMP._IOwnership _1666___v129;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1667_recIdents;
            RAST._IExpr _out417;
            DCOMP._IOwnership _out418;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out419;
            (this).GenExpr(_1663_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out417, out _out418, out _out419);
            _1665_recursiveGen = _out417;
            _1666___v129 = _out418;
            _1667_recIdents = _out419;
            r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _1665_recursiveGen, _1664_format);
            RAST._IExpr _out420;
            DCOMP._IOwnership _out421;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out420, out _out421);
            r = _out420;
            resultingOwnership = _out421;
            readIdents = _1667_recIdents;
            return ;
          }
          goto after_match30;
        }
      }
      if (_source74.is_UnOp) {
        DAST._IUnaryOp unOp1 = _source74.dtor_unOp;
        if (unOp1.is_BitwiseNot) {
          DAST._IExpression _1668_e = _source74.dtor_expr;
          DAST.Format._IUnaryOpFormat _1669_format = _source74.dtor_format1;
          {
            RAST._IExpr _1670_recursiveGen;
            DCOMP._IOwnership _1671___v130;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1672_recIdents;
            RAST._IExpr _out422;
            DCOMP._IOwnership _out423;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out424;
            (this).GenExpr(_1668_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out422, out _out423, out _out424);
            _1670_recursiveGen = _out422;
            _1671___v130 = _out423;
            _1672_recIdents = _out424;
            r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _1670_recursiveGen, _1669_format);
            RAST._IExpr _out425;
            DCOMP._IOwnership _out426;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out425, out _out426);
            r = _out425;
            resultingOwnership = _out426;
            readIdents = _1672_recIdents;
            return ;
          }
          goto after_match30;
        }
      }
      if (_source74.is_UnOp) {
        DAST._IUnaryOp unOp2 = _source74.dtor_unOp;
        if (unOp2.is_Cardinality) {
          DAST._IExpression _1673_e = _source74.dtor_expr;
          DAST.Format._IUnaryOpFormat _1674_format = _source74.dtor_format1;
          {
            RAST._IExpr _1675_recursiveGen;
            DCOMP._IOwnership _1676_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1677_recIdents;
            RAST._IExpr _out427;
            DCOMP._IOwnership _out428;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out429;
            (this).GenExpr(_1673_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out427, out _out428, out _out429);
            _1675_recursiveGen = _out427;
            _1676_recOwned = _out428;
            _1677_recIdents = _out429;
            r = ((_1675_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out430;
            DCOMP._IOwnership _out431;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out430, out _out431);
            r = _out430;
            resultingOwnership = _out431;
            readIdents = _1677_recIdents;
            return ;
          }
          goto after_match30;
        }
      }
      if (_source74.is_BinOp) {
        RAST._IExpr _out432;
        DCOMP._IOwnership _out433;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out434;
        (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out432, out _out433, out _out434);
        r = _out432;
        resultingOwnership = _out433;
        readIdents = _out434;
        goto after_match30;
      }
      if (_source74.is_ArrayLen) {
        DAST._IExpression _1678_expr = _source74.dtor_expr;
        BigInteger _1679_dim = _source74.dtor_dim;
        {
          RAST._IExpr _1680_recursiveGen;
          DCOMP._IOwnership _1681___v135;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1682_recIdents;
          RAST._IExpr _out435;
          DCOMP._IOwnership _out436;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out437;
          (this).GenExpr(_1678_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out435, out _out436, out _out437);
          _1680_recursiveGen = _out435;
          _1681___v135 = _out436;
          _1682_recIdents = _out437;
          if ((_1679_dim).Sign == 0) {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), (_1680_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())")));
          } else {
            Dafny.ISequence<Dafny.Rune> _1683_s;
            _1683_s = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(m.borrow().len())")))._ToString(DCOMP.__default.IND);
            BigInteger _1684_i;
            _1684_i = BigInteger.One;
            while ((_1684_i) < (_1679_dim)) {
              _1683_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("m.borrow().get(0).map(|m| "), _1683_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"));
              _1684_i = (_1684_i) + (BigInteger.One);
            }
            r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_1680_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow().get(0).map(|m| ")), _1683_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"))));
          }
          RAST._IExpr _out438;
          DCOMP._IOwnership _out439;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out438, out _out439);
          r = _out438;
          resultingOwnership = _out439;
          readIdents = _1682_recIdents;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_MapKeys) {
        DAST._IExpression _1685_expr = _source74.dtor_expr;
        {
          RAST._IExpr _1686_recursiveGen;
          DCOMP._IOwnership _1687___v136;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1688_recIdents;
          RAST._IExpr _out440;
          DCOMP._IOwnership _out441;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out442;
          (this).GenExpr(_1685_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out440, out _out441, out _out442);
          _1686_recursiveGen = _out440;
          _1687___v136 = _out441;
          _1688_recIdents = _out442;
          readIdents = _1688_recIdents;
          r = ((_1686_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out443;
          DCOMP._IOwnership _out444;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out443, out _out444);
          r = _out443;
          resultingOwnership = _out444;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_MapValues) {
        DAST._IExpression _1689_expr = _source74.dtor_expr;
        {
          RAST._IExpr _1690_recursiveGen;
          DCOMP._IOwnership _1691___v137;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1692_recIdents;
          RAST._IExpr _out445;
          DCOMP._IOwnership _out446;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out447;
          (this).GenExpr(_1689_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out445, out _out446, out _out447);
          _1690_recursiveGen = _out445;
          _1691___v137 = _out446;
          _1692_recIdents = _out447;
          readIdents = _1692_recIdents;
          r = ((_1690_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out448;
          DCOMP._IOwnership _out449;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out448, out _out449);
          r = _out448;
          resultingOwnership = _out449;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_SelectFn) {
        DAST._IExpression _1693_on = _source74.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _1694_field = _source74.dtor_field;
        bool _1695_isDatatype = _source74.dtor_onDatatype;
        bool _1696_isStatic = _source74.dtor_isStatic;
        BigInteger _1697_arity = _source74.dtor_arity;
        {
          RAST._IExpr _1698_onExpr;
          DCOMP._IOwnership _1699_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1700_recIdents;
          RAST._IExpr _out450;
          DCOMP._IOwnership _out451;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out452;
          (this).GenExpr(_1693_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out450, out _out451, out _out452);
          _1698_onExpr = _out450;
          _1699_onOwned = _out451;
          _1700_recIdents = _out452;
          Dafny.ISequence<Dafny.Rune> _1701_s = Dafny.Sequence<Dafny.Rune>.Empty;
          Dafny.ISequence<Dafny.Rune> _1702_onString;
          _1702_onString = (_1698_onExpr)._ToString(DCOMP.__default.IND);
          if (_1696_isStatic) {
            _1701_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1702_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_1694_field));
          } else {
            _1701_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
            _1701_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1701_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _1702_onString), ((object.Equals(_1699_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            Dafny.ISequence<Dafny.Rune> _1703_args;
            _1703_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            BigInteger _1704_i;
            _1704_i = BigInteger.Zero;
            while ((_1704_i) < (_1697_arity)) {
              if ((_1704_i).Sign == 1) {
                _1703_args = Dafny.Sequence<Dafny.Rune>.Concat(_1703_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _1703_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1703_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_1704_i));
              _1704_i = (_1704_i) + (BigInteger.One);
            }
            _1701_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1701_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _1703_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
            _1701_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1701_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_1694_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1703_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
            _1701_s = Dafny.Sequence<Dafny.Rune>.Concat(_1701_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            _1701_s = Dafny.Sequence<Dafny.Rune>.Concat(_1701_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
          }
          Dafny.ISequence<Dafny.Rune> _1705_typeShape;
          _1705_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
          BigInteger _1706_i;
          _1706_i = BigInteger.Zero;
          while ((_1706_i) < (_1697_arity)) {
            if ((_1706_i).Sign == 1) {
              _1705_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1705_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            _1705_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1705_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
            _1706_i = (_1706_i) + (BigInteger.One);
          }
          _1705_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1705_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
          _1701_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _1701_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _1705_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          r = RAST.Expr.create_RawExpr(_1701_s);
          RAST._IExpr _out453;
          DCOMP._IOwnership _out454;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out453, out _out454);
          r = _out453;
          resultingOwnership = _out454;
          readIdents = _1700_recIdents;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_Select) {
        DAST._IExpression expr0 = _source74.dtor_expr;
        if (expr0.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1707_c = expr0.dtor_Companion_a0;
          Dafny.ISequence<Dafny.Rune> _1708_field = _source74.dtor_field;
          bool _1709_isConstant = _source74.dtor_isConstant;
          bool _1710_isDatatype = _source74.dtor_onDatatype;
          DAST._IType _1711_fieldType = _source74.dtor_fieldType;
          {
            RAST._IExpr _1712_onExpr;
            DCOMP._IOwnership _1713_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1714_recIdents;
            RAST._IExpr _out455;
            DCOMP._IOwnership _out456;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out457;
            (this).GenExpr(DAST.Expression.create_Companion(_1707_c), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out455, out _out456, out _out457);
            _1712_onExpr = _out455;
            _1713_onOwned = _out456;
            _1714_recIdents = _out457;
            r = ((_1712_onExpr).MSel(DCOMP.__default.escapeName(_1708_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out458;
            DCOMP._IOwnership _out459;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out458, out _out459);
            r = _out458;
            resultingOwnership = _out459;
            readIdents = _1714_recIdents;
            return ;
          }
          goto after_match30;
        }
      }
      if (_source74.is_Select) {
        DAST._IExpression _1715_on = _source74.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _1716_field = _source74.dtor_field;
        bool _1717_isConstant = _source74.dtor_isConstant;
        bool _1718_isDatatype = _source74.dtor_onDatatype;
        DAST._IType _1719_fieldType = _source74.dtor_fieldType;
        {
          if (_1718_isDatatype) {
            RAST._IExpr _1720_onExpr;
            DCOMP._IOwnership _1721_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1722_recIdents;
            RAST._IExpr _out460;
            DCOMP._IOwnership _out461;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out462;
            (this).GenExpr(_1715_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out460, out _out461, out _out462);
            _1720_onExpr = _out460;
            _1721_onOwned = _out461;
            _1722_recIdents = _out462;
            r = ((_1720_onExpr).Sel(DCOMP.__default.escapeName(_1716_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IType _1723_typ;
            RAST._IType _out463;
            _out463 = (this).GenType(_1719_fieldType, false, false);
            _1723_typ = _out463;
            RAST._IExpr _out464;
            DCOMP._IOwnership _out465;
            DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out464, out _out465);
            r = _out464;
            resultingOwnership = _out465;
            readIdents = _1722_recIdents;
          } else {
            RAST._IExpr _1724_onExpr;
            DCOMP._IOwnership _1725_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1726_recIdents;
            RAST._IExpr _out466;
            DCOMP._IOwnership _out467;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out468;
            (this).GenExpr(_1715_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out466, out _out467, out _out468);
            _1724_onExpr = _out466;
            _1725_onOwned = _out467;
            _1726_recIdents = _out468;
            r = _1724_onExpr;
            r = (r).Sel(DCOMP.__default.escapeName(_1716_field));
            if (_1717_isConstant) {
              r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            } else {
              Dafny.ISequence<Dafny.Rune> _1727_s;
              _1727_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_1724_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_1716_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              r = RAST.Expr.create_RawExpr(_1727_s);
            }
            DCOMP._IOwnership _1728_fromOwnership;
            if (_1717_isConstant) {
              _1728_fromOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else {
              _1728_fromOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            }
            RAST._IExpr _out469;
            DCOMP._IOwnership _out470;
            DCOMP.COMP.FromOwnership(r, _1728_fromOwnership, expectedOwnership, out _out469, out _out470);
            r = _out469;
            resultingOwnership = _out470;
            readIdents = _1726_recIdents;
          }
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_Index) {
        DAST._IExpression _1729_on = _source74.dtor_expr;
        DAST._ICollKind _1730_collKind = _source74.dtor_collKind;
        Dafny.ISequence<DAST._IExpression> _1731_indices = _source74.dtor_indices;
        {
          RAST._IExpr _1732_onExpr;
          DCOMP._IOwnership _1733_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1734_recIdents;
          RAST._IExpr _out471;
          DCOMP._IOwnership _out472;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out473;
          (this).GenExpr(_1729_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out471, out _out472, out _out473);
          _1732_onExpr = _out471;
          _1733_onOwned = _out472;
          _1734_recIdents = _out473;
          readIdents = _1734_recIdents;
          r = _1732_onExpr;
          BigInteger _1735_i;
          _1735_i = BigInteger.Zero;
          while ((_1735_i) < (new BigInteger((_1731_indices).Count))) {
            if (object.Equals(_1730_collKind, DAST.CollKind.create_Array())) {
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IExpr _1736_idx;
            DCOMP._IOwnership _1737_idxOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1738_recIdentsIdx;
            RAST._IExpr _out474;
            DCOMP._IOwnership _out475;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out476;
            (this).GenExpr((_1731_indices).Select(_1735_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out474, out _out475, out _out476);
            _1736_idx = _out474;
            _1737_idxOwned = _out475;
            _1738_recIdentsIdx = _out476;
            r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_1736_idx);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1738_recIdentsIdx);
            _1735_i = (_1735_i) + (BigInteger.One);
          }
          RAST._IExpr _out477;
          DCOMP._IOwnership _out478;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out477, out _out478);
          r = _out477;
          resultingOwnership = _out478;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_IndexRange) {
        DAST._IExpression _1739_on = _source74.dtor_expr;
        bool _1740_isArray = _source74.dtor_isArray;
        Std.Wrappers._IOption<DAST._IExpression> _1741_low = _source74.dtor_low;
        Std.Wrappers._IOption<DAST._IExpression> _1742_high = _source74.dtor_high;
        {
          RAST._IExpr _1743_onExpr;
          DCOMP._IOwnership _1744_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1745_recIdents;
          RAST._IExpr _out479;
          DCOMP._IOwnership _out480;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out481;
          (this).GenExpr(_1739_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out479, out _out480, out _out481);
          _1743_onExpr = _out479;
          _1744_onOwned = _out480;
          _1745_recIdents = _out481;
          readIdents = _1745_recIdents;
          Dafny.ISequence<Dafny.Rune> _1746_methodName;
          if ((_1741_low).is_Some) {
            if ((_1742_high).is_Some) {
              _1746_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice");
            } else {
              _1746_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop");
            }
          } else if ((_1742_high).is_Some) {
            _1746_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take");
          } else {
            _1746_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          }
          Dafny.ISequence<RAST._IExpr> _1747_arguments;
          _1747_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          Std.Wrappers._IOption<DAST._IExpression> _source76 = _1741_low;
          if (_source76.is_Some) {
            DAST._IExpression _1748_l = _source76.dtor_value;
            {
              RAST._IExpr _1749_lExpr;
              DCOMP._IOwnership _1750___v138;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1751_recIdentsL;
              RAST._IExpr _out482;
              DCOMP._IOwnership _out483;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out484;
              (this).GenExpr(_1748_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out482, out _out483, out _out484);
              _1749_lExpr = _out482;
              _1750___v138 = _out483;
              _1751_recIdentsL = _out484;
              _1747_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1747_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1749_lExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1751_recIdentsL);
            }
            goto after_match32;
          }
        after_match32: ;
          Std.Wrappers._IOption<DAST._IExpression> _source77 = _1742_high;
          if (_source77.is_Some) {
            DAST._IExpression _1752_h = _source77.dtor_value;
            {
              RAST._IExpr _1753_hExpr;
              DCOMP._IOwnership _1754___v139;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1755_recIdentsH;
              RAST._IExpr _out485;
              DCOMP._IOwnership _out486;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out487;
              (this).GenExpr(_1752_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out485, out _out486, out _out487);
              _1753_hExpr = _out485;
              _1754___v139 = _out486;
              _1755_recIdentsH = _out487;
              _1747_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1747_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1753_hExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1755_recIdentsH);
            }
            goto after_match33;
          }
        after_match33: ;
          r = _1743_onExpr;
          if (_1740_isArray) {
            if (!(_1746_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
              _1746_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1746_methodName);
            }
            r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _1746_methodName))).Apply(_1747_arguments);
          } else {
            if (!(_1746_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
              r = ((r).Sel(_1746_methodName)).Apply(_1747_arguments);
            }
          }
          RAST._IExpr _out488;
          DCOMP._IOwnership _out489;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out488, out _out489);
          r = _out488;
          resultingOwnership = _out489;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_TupleSelect) {
        DAST._IExpression _1756_on = _source74.dtor_expr;
        BigInteger _1757_idx = _source74.dtor_index;
        DAST._IType _1758_fieldType = _source74.dtor_fieldType;
        {
          RAST._IExpr _1759_onExpr;
          DCOMP._IOwnership _1760_onOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1761_recIdents;
          RAST._IExpr _out490;
          DCOMP._IOwnership _out491;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out492;
          (this).GenExpr(_1756_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out490, out _out491, out _out492);
          _1759_onExpr = _out490;
          _1760_onOwnership = _out491;
          _1761_recIdents = _out492;
          Dafny.ISequence<Dafny.Rune> _1762_selName;
          _1762_selName = Std.Strings.__default.OfNat(_1757_idx);
          DAST._IType _source78 = _1758_fieldType;
          if (_source78.is_Tuple) {
            Dafny.ISequence<DAST._IType> _1763_tps = _source78.dtor_Tuple_a0;
            if (((_1758_fieldType).is_Tuple) && ((new BigInteger((_1763_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
              _1762_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1762_selName);
            }
            goto after_match34;
          }
        after_match34: ;
          r = (_1759_onExpr).Sel(_1762_selName);
          RAST._IExpr _out493;
          DCOMP._IOwnership _out494;
          DCOMP.COMP.FromOwnership(r, _1760_onOwnership, expectedOwnership, out _out493, out _out494);
          r = _out493;
          resultingOwnership = _out494;
          readIdents = _1761_recIdents;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_Call) {
        DAST._IExpression _1764_on = _source74.dtor_on;
        DAST._ICallName _1765_name = _source74.dtor_callName;
        Dafny.ISequence<DAST._IType> _1766_typeArgs = _source74.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _1767_args = _source74.dtor_args;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          RAST._IExpr _1768_onExpr;
          DCOMP._IOwnership _1769___v141;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1770_recIdents;
          RAST._IExpr _out495;
          DCOMP._IOwnership _out496;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out497;
          (this).GenExpr(_1764_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out495, out _out496, out _out497);
          _1768_onExpr = _out495;
          _1769___v141 = _out496;
          _1770_recIdents = _out497;
          Dafny.ISequence<RAST._IType> _1771_typeExprs;
          _1771_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
          if ((new BigInteger((_1766_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _hi35 = new BigInteger((_1766_typeArgs).Count);
            for (BigInteger _1772_typeI = BigInteger.Zero; _1772_typeI < _hi35; _1772_typeI++) {
              RAST._IType _1773_typeExpr;
              RAST._IType _out498;
              _out498 = (this).GenType((_1766_typeArgs).Select(_1772_typeI), false, false);
              _1773_typeExpr = _out498;
              _1771_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1771_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1773_typeExpr));
            }
          }
          Dafny.ISequence<RAST._IExpr> _1774_argExprs;
          _1774_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi36 = new BigInteger((_1767_args).Count);
          for (BigInteger _1775_i = BigInteger.Zero; _1775_i < _hi36; _1775_i++) {
            DCOMP._IOwnership _1776_argOwnership;
            _1776_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            if (((_1765_name).is_CallName) && ((_1775_i) < (new BigInteger((((_1765_name).dtor_signature)).Count)))) {
              RAST._IType _1777_tpe;
              RAST._IType _out499;
              _out499 = (this).GenType(((((_1765_name).dtor_signature)).Select(_1775_i)).dtor_typ, false, false);
              _1777_tpe = _out499;
              if ((_1777_tpe).CanReadWithoutClone()) {
                _1776_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
              }
            }
            RAST._IExpr _1778_argExpr;
            DCOMP._IOwnership _1779___v142;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1780_argIdents;
            RAST._IExpr _out500;
            DCOMP._IOwnership _out501;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out502;
            (this).GenExpr((_1767_args).Select(_1775_i), selfIdent, env, _1776_argOwnership, out _out500, out _out501, out _out502);
            _1778_argExpr = _out500;
            _1779___v142 = _out501;
            _1780_argIdents = _out502;
            _1774_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1774_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1778_argExpr));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1780_argIdents);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1770_recIdents);
          Dafny.ISequence<Dafny.Rune> _1781_renderedName;
          DAST._ICallName _source79 = _1765_name;
          if (_source79.is_CallName) {
            Dafny.ISequence<Dafny.Rune> _1782_ident = _source79.dtor_name;
            _1781_renderedName = DCOMP.__default.escapeName(_1782_ident);
            goto after_match35;
          }
          bool disjunctiveMatch11 = false;
          if (_source79.is_MapBuilderAdd) {
            disjunctiveMatch11 = true;
          }
          if (_source79.is_SetBuilderAdd) {
            disjunctiveMatch11 = true;
          }
          if (disjunctiveMatch11) {
            _1781_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            goto after_match35;
          }
          _1781_renderedName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
        after_match35: ;
          DAST._IExpression _source80 = _1764_on;
          if (_source80.is_Companion) {
            {
              _1768_onExpr = (_1768_onExpr).MSel(_1781_renderedName);
            }
            goto after_match36;
          }
          {
            _1768_onExpr = (_1768_onExpr).Sel(_1781_renderedName);
          }
        after_match36: ;
          r = _1768_onExpr;
          if ((new BigInteger((_1771_typeExprs).Count)).Sign == 1) {
            r = (r).ApplyType(_1771_typeExprs);
          }
          r = (r).Apply(_1774_argExprs);
          RAST._IExpr _out503;
          DCOMP._IOwnership _out504;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out503, out _out504);
          r = _out503;
          resultingOwnership = _out504;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_Lambda) {
        Dafny.ISequence<DAST._IFormal> _1783_paramsDafny = _source74.dtor_params;
        DAST._IType _1784_retType = _source74.dtor_retType;
        Dafny.ISequence<DAST._IStatement> _1785_body = _source74.dtor_body;
        {
          Dafny.ISequence<RAST._IFormal> _1786_params;
          Dafny.ISequence<RAST._IFormal> _out505;
          _out505 = (this).GenParams(_1783_paramsDafny);
          _1786_params = _out505;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1787_paramNames;
          _1787_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1788_paramTypesMap;
          _1788_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
          BigInteger _hi37 = new BigInteger((_1786_params).Count);
          for (BigInteger _1789_i = BigInteger.Zero; _1789_i < _hi37; _1789_i++) {
            Dafny.ISequence<Dafny.Rune> _1790_name;
            _1790_name = ((_1786_params).Select(_1789_i)).dtor_name;
            _1787_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1787_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1790_name));
            _1788_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1788_paramTypesMap, _1790_name, ((_1786_params).Select(_1789_i)).dtor_tpe);
          }
          DCOMP._IEnvironment _1791_env;
          _1791_env = DCOMP.Environment.create(_1787_paramNames, _1788_paramTypesMap);
          RAST._IExpr _1792_recursiveGen;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1793_recIdents;
          DCOMP._IEnvironment _1794___v147;
          RAST._IExpr _out506;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out507;
          DCOMP._IEnvironment _out508;
          (this).GenStmts(_1785_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), _1791_env, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out506, out _out507, out _out508);
          _1792_recursiveGen = _out506;
          _1793_recIdents = _out507;
          _1794___v147 = _out508;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          _1793_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1793_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_1795_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
            var _coll6 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
            foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in (_1795_paramNames).CloneAsArray()) {
              Dafny.ISequence<Dafny.Rune> _1796_name = (Dafny.ISequence<Dafny.Rune>)_compr_6;
              if ((_1795_paramNames).Contains(_1796_name)) {
                _coll6.Add(_1796_name);
              }
            }
            return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll6);
          }))())(_1787_paramNames));
          RAST._IExpr _1797_allReadCloned;
          _1797_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          while (!(_1793_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
            Dafny.ISequence<Dafny.Rune> _1798_next;
            foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_1793_recIdents).Elements) {
              _1798_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
              if ((_1793_recIdents).Contains(_1798_next)) {
                goto after__ASSIGN_SUCH_THAT_3;
              }
            }
            throw new System.Exception("assign-such-that search produced no value (line 3735)");
          after__ASSIGN_SUCH_THAT_3: ;
            if ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) && ((_1798_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
              if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
                _1797_allReadCloned = (_1797_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
              }
            } else if (!((_1787_paramNames).Contains(_1798_next))) {
              _1797_allReadCloned = (_1797_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1798_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.Expr.create_Identifier(_1798_next)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1798_next));
            }
            _1793_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1793_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1798_next));
          }
          RAST._IType _1799_retTypeGen;
          RAST._IType _out509;
          _out509 = (this).GenType(_1784_retType, false, true);
          _1799_retTypeGen = _out509;
          r = RAST.Expr.create_Block((_1797_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_1786_params, Std.Wrappers.Option<RAST._IType>.create_Some(_1799_retTypeGen), RAST.Expr.create_Block(_1792_recursiveGen)))));
          RAST._IExpr _out510;
          DCOMP._IOwnership _out511;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out510, out _out511);
          r = _out510;
          resultingOwnership = _out511;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_BetaRedex) {
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _1800_values = _source74.dtor_values;
        DAST._IType _1801_retType = _source74.dtor_retType;
        DAST._IExpression _1802_expr = _source74.dtor_expr;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1803_paramNames;
          _1803_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<RAST._IFormal> _1804_paramFormals;
          Dafny.ISequence<RAST._IFormal> _out512;
          _out512 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_1805_value) => {
            return (_1805_value).dtor__0;
          })), _1800_values));
          _1804_paramFormals = _out512;
          Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1806_paramTypes;
          _1806_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1807_paramNamesSet;
          _1807_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _hi38 = new BigInteger((_1800_values).Count);
          for (BigInteger _1808_i = BigInteger.Zero; _1808_i < _hi38; _1808_i++) {
            Dafny.ISequence<Dafny.Rune> _1809_name;
            _1809_name = (((_1800_values).Select(_1808_i)).dtor__0).dtor_name;
            Dafny.ISequence<Dafny.Rune> _1810_rName;
            _1810_rName = DCOMP.__default.escapeName(_1809_name);
            _1803_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1803_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1810_rName));
            _1806_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1806_paramTypes, _1810_rName, ((_1804_paramFormals).Select(_1808_i)).dtor_tpe);
            _1807_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1807_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1810_rName));
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          BigInteger _hi39 = new BigInteger((_1800_values).Count);
          for (BigInteger _1811_i = BigInteger.Zero; _1811_i < _hi39; _1811_i++) {
            RAST._IType _1812_typeGen;
            RAST._IType _out513;
            _out513 = (this).GenType((((_1800_values).Select(_1811_i)).dtor__0).dtor_typ, false, true);
            _1812_typeGen = _out513;
            RAST._IExpr _1813_valueGen;
            DCOMP._IOwnership _1814___v148;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1815_recIdents;
            RAST._IExpr _out514;
            DCOMP._IOwnership _out515;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out516;
            (this).GenExpr(((_1800_values).Select(_1811_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out514, out _out515, out _out516);
            _1813_valueGen = _out514;
            _1814___v148 = _out515;
            _1815_recIdents = _out516;
            r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_1800_values).Select(_1811_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1812_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1813_valueGen)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1815_recIdents);
          }
          DCOMP._IEnvironment _1816_newEnv;
          _1816_newEnv = DCOMP.Environment.create(_1803_paramNames, _1806_paramTypes);
          RAST._IExpr _1817_recGen;
          DCOMP._IOwnership _1818_recOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1819_recIdents;
          RAST._IExpr _out517;
          DCOMP._IOwnership _out518;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out519;
          (this).GenExpr(_1802_expr, selfIdent, _1816_newEnv, expectedOwnership, out _out517, out _out518, out _out519);
          _1817_recGen = _out517;
          _1818_recOwned = _out518;
          _1819_recIdents = _out519;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1819_recIdents, _1807_paramNamesSet);
          r = RAST.Expr.create_Block((r).Then(_1817_recGen));
          RAST._IExpr _out520;
          DCOMP._IOwnership _out521;
          DCOMP.COMP.FromOwnership(r, _1818_recOwned, expectedOwnership, out _out520, out _out521);
          r = _out520;
          resultingOwnership = _out521;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_IIFE) {
        Dafny.ISequence<Dafny.Rune> _1820_name = _source74.dtor_name;
        DAST._IType _1821_tpe = _source74.dtor_typ;
        DAST._IExpression _1822_value = _source74.dtor_value;
        DAST._IExpression _1823_iifeBody = _source74.dtor_iifeBody;
        {
          RAST._IExpr _1824_valueGen;
          DCOMP._IOwnership _1825___v149;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1826_recIdents;
          RAST._IExpr _out522;
          DCOMP._IOwnership _out523;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out524;
          (this).GenExpr(_1822_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out522, out _out523, out _out524);
          _1824_valueGen = _out522;
          _1825___v149 = _out523;
          _1826_recIdents = _out524;
          readIdents = _1826_recIdents;
          RAST._IType _1827_valueTypeGen;
          RAST._IType _out525;
          _out525 = (this).GenType(_1821_tpe, false, true);
          _1827_valueTypeGen = _out525;
          RAST._IExpr _1828_bodyGen;
          DCOMP._IOwnership _1829___v150;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1830_bodyIdents;
          RAST._IExpr _out526;
          DCOMP._IOwnership _out527;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out528;
          (this).GenExpr(_1823_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out526, out _out527, out _out528);
          _1828_bodyGen = _out526;
          _1829___v150 = _out527;
          _1830_bodyIdents = _out528;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1830_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_1820_name)))));
          r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_1820_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_1827_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1824_valueGen))).Then(_1828_bodyGen));
          RAST._IExpr _out529;
          DCOMP._IOwnership _out530;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out529, out _out530);
          r = _out529;
          resultingOwnership = _out530;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_Apply) {
        DAST._IExpression _1831_func = _source74.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1832_args = _source74.dtor_args;
        {
          RAST._IExpr _1833_funcExpr;
          DCOMP._IOwnership _1834___v151;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1835_recIdents;
          RAST._IExpr _out531;
          DCOMP._IOwnership _out532;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out533;
          (this).GenExpr(_1831_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out531, out _out532, out _out533);
          _1833_funcExpr = _out531;
          _1834___v151 = _out532;
          _1835_recIdents = _out533;
          readIdents = _1835_recIdents;
          Dafny.ISequence<RAST._IExpr> _1836_rArgs;
          _1836_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi40 = new BigInteger((_1832_args).Count);
          for (BigInteger _1837_i = BigInteger.Zero; _1837_i < _hi40; _1837_i++) {
            RAST._IExpr _1838_argExpr;
            DCOMP._IOwnership _1839_argOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1840_argIdents;
            RAST._IExpr _out534;
            DCOMP._IOwnership _out535;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out536;
            (this).GenExpr((_1832_args).Select(_1837_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out534, out _out535, out _out536);
            _1838_argExpr = _out534;
            _1839_argOwned = _out535;
            _1840_argIdents = _out536;
            _1836_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1836_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1838_argExpr));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1840_argIdents);
          }
          r = (_1833_funcExpr).Apply(_1836_rArgs);
          RAST._IExpr _out537;
          DCOMP._IOwnership _out538;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out537, out _out538);
          r = _out537;
          resultingOwnership = _out538;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_TypeTest) {
        DAST._IExpression _1841_on = _source74.dtor_on;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1842_dType = _source74.dtor_dType;
        Dafny.ISequence<Dafny.Rune> _1843_variant = _source74.dtor_variant;
        {
          RAST._IExpr _1844_exprGen;
          DCOMP._IOwnership _1845___v152;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1846_recIdents;
          RAST._IExpr _out539;
          DCOMP._IOwnership _out540;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
          (this).GenExpr(_1841_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out539, out _out540, out _out541);
          _1844_exprGen = _out539;
          _1845___v152 = _out540;
          _1846_recIdents = _out541;
          RAST._IType _1847_dTypePath;
          RAST._IType _out542;
          _out542 = DCOMP.COMP.GenPath(_1842_dType);
          _1847_dTypePath = _out542;
          r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_1844_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_1847_dTypePath).MSel(DCOMP.__default.escapeName(_1843_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
          RAST._IExpr _out543;
          DCOMP._IOwnership _out544;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out543, out _out544);
          r = _out543;
          resultingOwnership = _out544;
          readIdents = _1846_recIdents;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_BoolBoundedPool) {
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
        goto after_match30;
      }
      if (_source74.is_SetBoundedPool) {
        DAST._IExpression _1848_of = _source74.dtor_of;
        {
          RAST._IExpr _1849_exprGen;
          DCOMP._IOwnership _1850___v153;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1851_recIdents;
          RAST._IExpr _out547;
          DCOMP._IOwnership _out548;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out549;
          (this).GenExpr(_1848_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out547, out _out548, out _out549);
          _1849_exprGen = _out547;
          _1850___v153 = _out548;
          _1851_recIdents = _out549;
          r = ((((_1849_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out550;
          DCOMP._IOwnership _out551;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out550, out _out551);
          r = _out550;
          resultingOwnership = _out551;
          readIdents = _1851_recIdents;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_SeqBoundedPool) {
        DAST._IExpression _1852_of = _source74.dtor_of;
        bool _1853_includeDuplicates = _source74.dtor_includeDuplicates;
        {
          RAST._IExpr _1854_exprGen;
          DCOMP._IOwnership _1855___v154;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1856_recIdents;
          RAST._IExpr _out552;
          DCOMP._IOwnership _out553;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out554;
          (this).GenExpr(_1852_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out552, out _out553, out _out554);
          _1854_exprGen = _out552;
          _1855___v154 = _out553;
          _1856_recIdents = _out554;
          r = ((_1854_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          if (!(_1853_includeDuplicates)) {
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
          }
          RAST._IExpr _out555;
          DCOMP._IOwnership _out556;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out555, out _out556);
          r = _out555;
          resultingOwnership = _out556;
          readIdents = _1856_recIdents;
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_IntRange) {
        DAST._IExpression _1857_lo = _source74.dtor_lo;
        DAST._IExpression _1858_hi = _source74.dtor_hi;
        {
          RAST._IExpr _1859_lo;
          DCOMP._IOwnership _1860___v155;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1861_recIdentsLo;
          RAST._IExpr _out557;
          DCOMP._IOwnership _out558;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out559;
          (this).GenExpr(_1857_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out557, out _out558, out _out559);
          _1859_lo = _out557;
          _1860___v155 = _out558;
          _1861_recIdentsLo = _out559;
          RAST._IExpr _1862_hi;
          DCOMP._IOwnership _1863___v156;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1864_recIdentsHi;
          RAST._IExpr _out560;
          DCOMP._IOwnership _out561;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out562;
          (this).GenExpr(_1858_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out560, out _out561, out _out562);
          _1862_hi = _out560;
          _1863___v156 = _out561;
          _1864_recIdentsHi = _out562;
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1859_lo, _1862_hi));
          RAST._IExpr _out563;
          DCOMP._IOwnership _out564;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out563, out _out564);
          r = _out563;
          resultingOwnership = _out564;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1861_recIdentsLo, _1864_recIdentsHi);
          return ;
        }
        goto after_match30;
      }
      if (_source74.is_MapBuilder) {
        DAST._IType _1865_keyType = _source74.dtor_keyType;
        DAST._IType _1866_valueType = _source74.dtor_valueType;
        {
          RAST._IType _1867_kType;
          RAST._IType _out565;
          _out565 = (this).GenType(_1865_keyType, false, false);
          _1867_kType = _out565;
          RAST._IType _1868_vType;
          RAST._IType _out566;
          _out566 = (this).GenType(_1866_valueType, false, false);
          _1868_vType = _out566;
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1867_kType, _1868_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out567;
          DCOMP._IOwnership _out568;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out567, out _out568);
          r = _out567;
          resultingOwnership = _out568;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
        goto after_match30;
      }
      DAST._IType _1869_elemType = _source74.dtor_elemType;
      {
        RAST._IType _1870_eType;
        RAST._IType _out569;
        _out569 = (this).GenType(_1869_elemType, false, false);
        _1870_eType = _out569;
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1870_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        RAST._IExpr _out570;
        DCOMP._IOwnership _out571;
        DCOMP.COMP.FromOwned(r, expectedOwnership, out _out570, out _out571);
        r = _out570;
        resultingOwnership = _out571;
        return ;
      }
    after_match30: ;
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      BigInteger _1871_i;
      _1871_i = BigInteger.Zero;
      while ((_1871_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _1872_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _1873_m;
        RAST._IMod _out572;
        _out572 = (this).GenModule((p).Select(_1871_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _1873_m = _out572;
        _1872_generated = (_1873_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_1871_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _1872_generated);
        _1871_i = (_1871_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _1874_i;
      _1874_i = BigInteger.Zero;
      while ((_1874_i) < (new BigInteger((fullName).Count))) {
        if ((_1874_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_1874_i)));
        _1874_i = (_1874_i) + (BigInteger.One);
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