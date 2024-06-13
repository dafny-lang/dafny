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
            Dafny.ISequence<Dafny.Rune> _in113 = (i).Drop(new BigInteger(2));
            i = _in113;
            goto TAIL_CALL_START;
          }
        } else {
          return true;
        }
      } else {
        Dafny.ISequence<Dafny.Rune> _in114 = (i).Drop(BigInteger.One);
        i = _in114;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> idiomatic__rust(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1032___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1032___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1032___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1032___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in115 = (i).Drop(new BigInteger(2));
        i = _in115;
        goto TAIL_CALL_START;
      } else {
        _1032___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1032___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in116 = (i).Drop(BigInteger.One);
        i = _in116;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1033___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1033___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1033___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1033___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in117 = (i).Drop(BigInteger.One);
        i = _in117;
        goto TAIL_CALL_START;
      } else {
        _1033___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1033___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in118 = (i).Drop(BigInteger.One);
        i = _in118;
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
        Dafny.ISequence<Dafny.Rune> _1034_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1034_r);
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
      BigInteger _1035_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1035_indexInEnv), ((this).dtor_names).Drop((_1035_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
      Dafny.ISequence<Dafny.Rune> _1036_modName;
      _1036_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_1036_modName);
      } else {
        Dafny.ISequence<RAST._IModDecl> _1037_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _1037_body = _out15;
        s = RAST.Mod.create_Mod(_1036_modName, _1037_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi5 = new BigInteger((body).Count);
      for (BigInteger _1038_i = BigInteger.Zero; _1038_i < _hi5; _1038_i++) {
        Dafny.ISequence<RAST._IModDecl> _1039_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source44 = (body).Select(_1038_i);
        bool unmatched44 = true;
        if (unmatched44) {
          if (_source44.is_Module) {
            DAST._IModule _1040_m = _source44.dtor_Module_a0;
            unmatched44 = false;
            RAST._IMod _1041_mm;
            RAST._IMod _out16;
            _out16 = (this).GenModule(_1040_m, containingPath);
            _1041_mm = _out16;
            _1039_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1041_mm));
          }
        }
        if (unmatched44) {
          if (_source44.is_Class) {
            DAST._IClass _1042_c = _source44.dtor_Class_a0;
            unmatched44 = false;
            Dafny.ISequence<RAST._IModDecl> _out17;
            _out17 = (this).GenClass(_1042_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1042_c).dtor_name)));
            _1039_generated = _out17;
          }
        }
        if (unmatched44) {
          if (_source44.is_Trait) {
            DAST._ITrait _1043_t = _source44.dtor_Trait_a0;
            unmatched44 = false;
            Dafny.ISequence<Dafny.Rune> _1044_tt;
            Dafny.ISequence<Dafny.Rune> _out18;
            _out18 = (this).GenTrait(_1043_t, containingPath);
            _1044_tt = _out18;
            _1039_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_RawDecl(_1044_tt));
          }
        }
        if (unmatched44) {
          if (_source44.is_Newtype) {
            DAST._INewtype _1045_n = _source44.dtor_Newtype_a0;
            unmatched44 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenNewtype(_1045_n);
            _1039_generated = _out19;
          }
        }
        if (unmatched44) {
          DAST._IDatatype _1046_d = _source44.dtor_Datatype_a0;
          unmatched44 = false;
          Dafny.ISequence<RAST._IModDecl> _out20;
          _out20 = (this).GenDatatype(_1046_d);
          _1039_generated = _out20;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1039_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1047_genTpConstraint;
      _1047_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1047_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1047_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1047_genTpConstraint);
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
        for (BigInteger _1048_tpI = BigInteger.Zero; _1048_tpI < _hi6; _1048_tpI++) {
          DAST._ITypeArgDecl _1049_tp;
          _1049_tp = (@params).Select(_1048_tpI);
          DAST._IType _1050_typeArg;
          RAST._ITypeParamDecl _1051_typeParam;
          DAST._IType _out21;
          RAST._ITypeParamDecl _out22;
          (this).GenTypeParam(_1049_tp, out _out21, out _out22);
          _1050_typeArg = _out21;
          _1051_typeParam = _out22;
          RAST._IType _1052_rType;
          RAST._IType _out23;
          _out23 = (this).GenType(_1050_typeArg, false, false);
          _1052_rType = _out23;
          typeParamsSet = Dafny.Set<DAST._IType>.Union(typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1050_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1052_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1051_typeParam));
        }
      }
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1053_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1054_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1055_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1056_whereConstraints;
      Dafny.ISet<DAST._IType> _out24;
      Dafny.ISequence<RAST._IType> _out25;
      Dafny.ISequence<RAST._ITypeParamDecl> _out26;
      Dafny.ISequence<Dafny.Rune> _out27;
      (this).GenTypeParameters((c).dtor_typeParams, out _out24, out _out25, out _out26, out _out27);
      _1053_typeParamsSet = _out24;
      _1054_rTypeParams = _out25;
      _1055_rTypeParamsDecls = _out26;
      _1056_whereConstraints = _out27;
      Dafny.ISequence<Dafny.Rune> _1057_constrainedTypeParams;
      _1057_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1055_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1058_fields;
      _1058_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1059_fieldInits;
      _1059_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1060_fieldI = BigInteger.Zero; _1060_fieldI < _hi7; _1060_fieldI++) {
        DAST._IField _1061_field;
        _1061_field = ((c).dtor_fields).Select(_1060_fieldI);
        RAST._IType _1062_fieldType;
        RAST._IType _out28;
        _out28 = (this).GenType(((_1061_field).dtor_formal).dtor_typ, false, false);
        _1062_fieldType = _out28;
        Dafny.ISequence<Dafny.Rune> _1063_fieldRustName;
        _1063_fieldRustName = DCOMP.__default.escapeName(((_1061_field).dtor_formal).dtor_name);
        _1058_fields = Dafny.Sequence<RAST._IField>.Concat(_1058_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1063_fieldRustName, _1062_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source45 = (_1061_field).dtor_defaultValue;
        bool unmatched45 = true;
        if (unmatched45) {
          if (_source45.is_Some) {
            DAST._IExpression _1064_e = _source45.dtor_value;
            unmatched45 = false;
            {
              RAST._IExpr _1065_expr;
              DCOMP._IOwnership _1066___v39;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1067___v40;
              RAST._IExpr _out29;
              DCOMP._IOwnership _out30;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out31;
              (this).GenExpr(_1064_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out29, out _out30, out _out31);
              _1065_expr = _out29;
              _1066___v39 = _out30;
              _1067___v40 = _out31;
              _1059_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1059_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1061_field).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cell::RefCell::new("), (_1065_expr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))))));
            }
          }
        }
        if (unmatched45) {
          unmatched45 = false;
          {
            RAST._IExpr _1068_default;
            _1068_default = RAST.__default.std__Default__default;
            _1059_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1059_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1063_fieldRustName, _1068_default)));
          }
        }
      }
      BigInteger _hi8 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1069_typeParamI = BigInteger.Zero; _1069_typeParamI < _hi8; _1069_typeParamI++) {
        DAST._IType _1070_typeArg;
        RAST._ITypeParamDecl _1071_typeParam;
        DAST._IType _out32;
        RAST._ITypeParamDecl _out33;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1069_typeParamI), out _out32, out _out33);
        _1070_typeArg = _out32;
        _1071_typeParam = _out33;
        RAST._IType _1072_rTypeArg;
        RAST._IType _out34;
        _out34 = (this).GenType(_1070_typeArg, false, false);
        _1072_rTypeArg = _out34;
        _1058_fields = Dafny.Sequence<RAST._IField>.Concat(_1058_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1069_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1072_rTypeArg))))));
        _1059_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1059_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1069_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      Dafny.ISequence<Dafny.Rune> _1073_datatypeName;
      _1073_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IStruct _1074_struct;
      _1074_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1073_datatypeName, _1055_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1058_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1074_struct));
      Dafny.ISequence<RAST._IImplMember> _1075_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1076_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out35;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out36;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(path, (c).dtor_attributes))), _1053_typeParamsSet, out _out35, out _out36);
      _1075_implBodyRaw = _out35;
      _1076_traitBodies = _out36;
      Dafny.ISequence<RAST._IImplMember> _1077_implBody;
      _1077_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(RAST.Expr.create_Identifier(_1073_datatypeName), _1059_fieldInits))))), _1075_implBodyRaw);
      RAST._IImpl _1078_i;
      _1078_i = RAST.Impl.create_Impl(_1055_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1073_datatypeName), _1054_rTypeParams), _1056_whereConstraints, _1077_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1078_i)));
      if ((new BigInteger(((c).dtor_superClasses).Count)).Sign == 1) {
        BigInteger _1079_i;
        _1079_i = BigInteger.Zero;
        while ((_1079_i) < (new BigInteger(((c).dtor_superClasses).Count))) {
          DAST._IType _1080_superClass;
          _1080_superClass = ((c).dtor_superClasses).Select(_1079_i);
          DAST._IType _source46 = _1080_superClass;
          bool unmatched46 = true;
          if (unmatched46) {
            if (_source46.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1081_traitPath = _source46.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _1082_typeArgs = _source46.dtor_typeArgs;
              DAST._IResolvedType resolved0 = _source46.dtor_resolved;
              if (resolved0.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1083___v41 = resolved0.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1084___v42 = resolved0.dtor_attributes;
                unmatched46 = false;
                {
                  RAST._IType _1085_pathStr;
                  RAST._IType _out37;
                  _out37 = DCOMP.COMP.GenPath(_1081_traitPath);
                  _1085_pathStr = _out37;
                  Dafny.ISequence<RAST._IType> _1086_typeArgs;
                  Dafny.ISequence<RAST._IType> _out38;
                  _out38 = (this).GenTypeArgs(_1082_typeArgs, false, false);
                  _1086_typeArgs = _out38;
                  Dafny.ISequence<RAST._IImplMember> _1087_body;
                  _1087_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((_1076_traitBodies).Contains(_1081_traitPath)) {
                    _1087_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1076_traitBodies,_1081_traitPath);
                  }
                  RAST._IType _1088_genSelfPath;
                  RAST._IType _out39;
                  _out39 = DCOMP.COMP.GenPath(path);
                  _1088_genSelfPath = _out39;
                  RAST._IModDecl _1089_x;
                  _1089_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1055_rTypeParamsDecls, RAST.Type.create_TypeApp(_1085_pathStr, _1086_typeArgs), RAST.__default.Rc(RAST.Type.create_TypeApp(_1088_genSelfPath, _1054_rTypeParams)), _1056_whereConstraints, _1087_body));
                  s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1089_x));
                }
              }
            }
          }
          if (unmatched46) {
            DAST._IType _1090___v43 = _source46;
            unmatched46 = false;
          }
          _1079_i = (_1079_i) + (BigInteger.One);
        }
      }
      RAST._IImpl _1091_d;
      _1091_d = RAST.Impl.create_ImplFor(_1055_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1073_datatypeName), _1054_rTypeParams), _1056_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(_1073_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new()"))))))));
      Dafny.ISequence<RAST._IModDecl> _1092_defaultImpl;
      _1092_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1091_d));
      RAST._IImpl _1093_p;
      _1093_p = RAST.Impl.create_ImplFor(_1055_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1073_datatypeName), _1054_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), DCOMP.__default.escapeName(((c).dtor_enclosingModule))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")"))))))));
      Dafny.ISequence<RAST._IModDecl> _1094_printImpl;
      _1094_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1093_p));
      RAST._IImpl _1095_pp;
      _1095_pp = RAST.Impl.create_ImplFor(_1055_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cmp::PartialEq")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1073_datatypeName), _1054_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("eq"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.__default.SelfBorrowed)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ptr::eq(self, other)")))))));
      Dafny.ISequence<RAST._IModDecl> _1096_ptrPartialEqImpl;
      _1096_ptrPartialEqImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1095_pp));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(s, _1092_defaultImpl), _1094_printImpl), _1096_ptrPartialEqImpl);
      return s;
    }
    public Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _1097_typeParamsSet;
      _1097_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1098_typeParamDecls;
      _1098_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1099_typeParams;
      _1099_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1100_tpI;
      _1100_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        while ((_1100_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._ITypeArgDecl _1101_tp;
          _1101_tp = ((t).dtor_typeParams).Select(_1100_tpI);
          DAST._IType _1102_typeArg;
          RAST._ITypeParamDecl _1103_typeParamDecl;
          DAST._IType _out40;
          RAST._ITypeParamDecl _out41;
          (this).GenTypeParam(_1101_tp, out _out40, out _out41);
          _1102_typeArg = _out40;
          _1103_typeParamDecl = _out41;
          _1097_typeParamsSet = Dafny.Set<DAST._IType>.Union(_1097_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1102_typeArg));
          _1098_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1098_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1103_typeParamDecl));
          RAST._IType _1104_typeParam;
          RAST._IType _out42;
          _out42 = (this).GenType(_1102_typeArg, false, false);
          _1104_typeParam = _out42;
          _1099_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1099_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1104_typeParam));
          _1100_tpI = (_1100_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1105_fullPath;
      _1105_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1106_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1107___v44;
      Dafny.ISequence<RAST._IImplMember> _out43;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out44;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_1105_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_1105_fullPath, (t).dtor_attributes)), _1097_typeParamsSet, out _out43, out _out44);
      _1106_implBody = _out43;
      _1107___v44 = _out44;
      s = (RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1098_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1099_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1106_implBody)))._ToString(DCOMP.__default.IND);
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1108_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1109_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1110_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1111_whereConstraints;
      Dafny.ISet<DAST._IType> _out45;
      Dafny.ISequence<RAST._IType> _out46;
      Dafny.ISequence<RAST._ITypeParamDecl> _out47;
      Dafny.ISequence<Dafny.Rune> _out48;
      (this).GenTypeParameters((c).dtor_typeParams, out _out45, out _out46, out _out47, out _out48);
      _1108_typeParamsSet = _out45;
      _1109_rTypeParams = _out46;
      _1110_rTypeParamsDecls = _out47;
      _1111_whereConstraints = _out48;
      Dafny.ISequence<Dafny.Rune> _1112_constrainedTypeParams;
      _1112_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1110_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1113_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source47 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      bool unmatched47 = true;
      if (unmatched47) {
        if (_source47.is_Some) {
          RAST._IType _1114_v = _source47.dtor_value;
          unmatched47 = false;
          _1113_underlyingType = _1114_v;
        }
      }
      if (unmatched47) {
        unmatched47 = false;
        RAST._IType _out49;
        _out49 = (this).GenType((c).dtor_base, false, false);
        _1113_underlyingType = _out49;
      }
      DAST._IType _1115_resultingType;
      _1115_resultingType = DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Newtype((c).dtor_base, (c).dtor_range, false, (c).dtor_attributes));
      Dafny.ISequence<Dafny.Rune> _1116_datatypeName;
      _1116_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1116_datatypeName, _1110_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1113_underlyingType))))));
      RAST._IExpr _1117_fnBody;
      _1117_fnBody = RAST.Expr.create_Identifier(_1116_datatypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source48 = (c).dtor_witnessExpr;
      bool unmatched48 = true;
      if (unmatched48) {
        if (_source48.is_Some) {
          DAST._IExpression _1118_e = _source48.dtor_value;
          unmatched48 = false;
          {
            DAST._IExpression _1119_e;
            _1119_e = ((object.Equals((c).dtor_base, _1115_resultingType)) ? (_1118_e) : (DAST.Expression.create_Convert(_1118_e, (c).dtor_base, _1115_resultingType)));
            RAST._IExpr _1120_eStr;
            DCOMP._IOwnership _1121___v45;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1122___v46;
            RAST._IExpr _out50;
            DCOMP._IOwnership _out51;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out52;
            (this).GenExpr(_1119_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out50, out _out51, out _out52);
            _1120_eStr = _out50;
            _1121___v45 = _out51;
            _1122___v46 = _out52;
            _1117_fnBody = (_1117_fnBody).Apply1(_1120_eStr);
          }
        }
      }
      if (unmatched48) {
        unmatched48 = false;
        {
          _1117_fnBody = (_1117_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1123_body;
      _1123_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1117_fnBody)));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1110_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1116_datatypeName), _1109_rTypeParams), _1111_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1123_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1110_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1116_datatypeName), _1109_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1110_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1116_datatypeName), _1109_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1113_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1124_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1125_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1126_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1127_whereConstraints;
      Dafny.ISet<DAST._IType> _out53;
      Dafny.ISequence<RAST._IType> _out54;
      Dafny.ISequence<RAST._ITypeParamDecl> _out55;
      Dafny.ISequence<Dafny.Rune> _out56;
      (this).GenTypeParameters((c).dtor_typeParams, out _out53, out _out54, out _out55, out _out56);
      _1124_typeParamsSet = _out53;
      _1125_rTypeParams = _out54;
      _1126_rTypeParamsDecls = _out55;
      _1127_whereConstraints = _out56;
      Dafny.ISequence<Dafny.Rune> _1128_datatypeName;
      _1128_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1129_ctors;
      _1129_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      BigInteger _hi9 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1130_i = BigInteger.Zero; _1130_i < _hi9; _1130_i++) {
        DAST._IDatatypeCtor _1131_ctor;
        _1131_ctor = ((c).dtor_ctors).Select(_1130_i);
        Dafny.ISequence<RAST._IField> _1132_ctorArgs;
        _1132_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1133_isNumeric;
        _1133_isNumeric = false;
        BigInteger _hi10 = new BigInteger(((_1131_ctor).dtor_args).Count);
        for (BigInteger _1134_j = BigInteger.Zero; _1134_j < _hi10; _1134_j++) {
          DAST._IDatatypeDtor _1135_dtor;
          _1135_dtor = ((_1131_ctor).dtor_args).Select(_1134_j);
          RAST._IType _1136_formalType;
          RAST._IType _out57;
          _out57 = (this).GenType(((_1135_dtor).dtor_formal).dtor_typ, false, false);
          _1136_formalType = _out57;
          Dafny.ISequence<Dafny.Rune> _1137_formalName;
          _1137_formalName = DCOMP.__default.escapeName(((_1135_dtor).dtor_formal).dtor_name);
          if (((_1134_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1137_formalName))) {
            _1133_isNumeric = true;
          }
          if ((((_1134_j).Sign != 0) && (_1133_isNumeric)) && (!(Std.Strings.__default.OfNat(_1134_j)).Equals(_1137_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1137_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1134_j)));
            _1133_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1132_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1132_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1137_formalName, RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1136_formalType))))));
          } else {
            _1132_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1132_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1137_formalName, _1136_formalType))));
          }
        }
        RAST._IFields _1138_namedFields;
        _1138_namedFields = RAST.Fields.create_NamedFields(_1132_ctorArgs);
        if (_1133_isNumeric) {
          _1138_namedFields = (_1138_namedFields).ToNamelessFields();
        }
        _1129_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1129_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1131_ctor).dtor_name), _1138_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1139_selfPath;
      _1139_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1140_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1141_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out58;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out59;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(_1139_selfPath, (c).dtor_attributes))), _1124_typeParamsSet, out _out58, out _out59);
      _1140_implBodyRaw = _out58;
      _1141_traitBodies = _out59;
      Dafny.ISequence<RAST._IImplMember> _1142_implBody;
      _1142_implBody = _1140_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1143_emittedFields;
      _1143_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi11 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1144_i = BigInteger.Zero; _1144_i < _hi11; _1144_i++) {
        DAST._IDatatypeCtor _1145_ctor;
        _1145_ctor = ((c).dtor_ctors).Select(_1144_i);
        BigInteger _hi12 = new BigInteger(((_1145_ctor).dtor_args).Count);
        for (BigInteger _1146_j = BigInteger.Zero; _1146_j < _hi12; _1146_j++) {
          DAST._IDatatypeDtor _1147_dtor;
          _1147_dtor = ((_1145_ctor).dtor_args).Select(_1146_j);
          Dafny.ISequence<Dafny.Rune> _1148_callName;
          _1148_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1147_dtor).dtor_callName, DCOMP.__default.escapeName(((_1147_dtor).dtor_formal).dtor_name));
          if (!((_1143_emittedFields).Contains(_1148_callName))) {
            _1143_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1143_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1148_callName));
            RAST._IType _1149_formalType;
            RAST._IType _out60;
            _out60 = (this).GenType(((_1147_dtor).dtor_formal).dtor_typ, false, false);
            _1149_formalType = _out60;
            Dafny.ISequence<RAST._IMatchCase> _1150_cases;
            _1150_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1151_k = BigInteger.Zero; _1151_k < _hi13; _1151_k++) {
              DAST._IDatatypeCtor _1152_ctor2;
              _1152_ctor2 = ((c).dtor_ctors).Select(_1151_k);
              Dafny.ISequence<Dafny.Rune> _1153_pattern;
              _1153_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1128_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1152_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1154_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1155_hasMatchingField;
              _1155_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1156_patternInner;
              _1156_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1157_isNumeric;
              _1157_isNumeric = false;
              BigInteger _hi14 = new BigInteger(((_1152_ctor2).dtor_args).Count);
              for (BigInteger _1158_l = BigInteger.Zero; _1158_l < _hi14; _1158_l++) {
                DAST._IDatatypeDtor _1159_dtor2;
                _1159_dtor2 = ((_1152_ctor2).dtor_args).Select(_1158_l);
                Dafny.ISequence<Dafny.Rune> _1160_patternName;
                _1160_patternName = DCOMP.__default.escapeName(((_1159_dtor2).dtor_formal).dtor_name);
                if (((_1158_l).Sign == 0) && ((_1160_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1157_isNumeric = true;
                }
                if (_1157_isNumeric) {
                  _1160_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1159_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1158_l)));
                }
                if (object.Equals(((_1147_dtor).dtor_formal).dtor_name, ((_1159_dtor2).dtor_formal).dtor_name)) {
                  _1155_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1160_patternName);
                }
                _1156_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1156_patternInner, _1160_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1157_isNumeric) {
                _1153_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1153_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1156_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1153_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1153_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1156_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1155_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1154_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1155_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1154_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1155_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1154_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _1161_ctorMatch;
              _1161_ctorMatch = RAST.MatchCase.create(_1153_pattern, RAST.Expr.create_RawExpr(_1154_rhs));
              _1150_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1150_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1161_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1150_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1150_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1128_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _1162_methodBody;
            _1162_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1150_cases);
            _1142_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1142_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1148_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1149_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1162_methodBody)))));
          }
        }
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1163_types;
        _1163_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi15 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1164_typeI = BigInteger.Zero; _1164_typeI < _hi15; _1164_typeI++) {
          DAST._IType _1165_typeArg;
          RAST._ITypeParamDecl _1166_rTypeParamDecl;
          DAST._IType _out61;
          RAST._ITypeParamDecl _out62;
          (this).GenTypeParam(((c).dtor_typeParams).Select(_1164_typeI), out _out61, out _out62);
          _1165_typeArg = _out61;
          _1166_rTypeParamDecl = _out62;
          RAST._IType _1167_rTypeArg;
          RAST._IType _out63;
          _out63 = (this).GenType(_1165_typeArg, false, false);
          _1167_rTypeArg = _out63;
          _1163_types = Dafny.Sequence<RAST._IType>.Concat(_1163_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1167_rTypeArg))));
        }
        _1129_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1129_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1168_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1168_tpe);
})), _1163_types)))));
      }
      Dafny.ISequence<RAST._IModDecl> _1169_enumBody;
      _1169_enumBody = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]")), _1128_datatypeName, _1126_rTypeParamsDecls, _1129_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1126_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1128_datatypeName), _1125_rTypeParams), _1127_whereConstraints, _1142_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1170_printImplBodyCases;
      _1170_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1171_i = BigInteger.Zero; _1171_i < _hi16; _1171_i++) {
        DAST._IDatatypeCtor _1172_ctor;
        _1172_ctor = ((c).dtor_ctors).Select(_1171_i);
        Dafny.ISequence<Dafny.Rune> _1173_ctorMatch;
        _1173_ctorMatch = DCOMP.__default.escapeName((_1172_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1174_modulePrefix;
        _1174_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1175_ctorName;
        _1175_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1174_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1172_ctor).dtor_name));
        if (((new BigInteger((_1175_ctorName).Count)) >= (new BigInteger(13))) && (((_1175_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1175_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1176_printRhs;
        _1176_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1175_ctorName), (((_1172_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        bool _1177_isNumeric;
        _1177_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1178_ctorMatchInner;
        _1178_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi17 = new BigInteger(((_1172_ctor).dtor_args).Count);
        for (BigInteger _1179_j = BigInteger.Zero; _1179_j < _hi17; _1179_j++) {
          DAST._IDatatypeDtor _1180_dtor;
          _1180_dtor = ((_1172_ctor).dtor_args).Select(_1179_j);
          Dafny.ISequence<Dafny.Rune> _1181_patternName;
          _1181_patternName = DCOMP.__default.escapeName(((_1180_dtor).dtor_formal).dtor_name);
          if (((_1179_j).Sign == 0) && ((_1181_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1177_isNumeric = true;
          }
          if (_1177_isNumeric) {
            _1181_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1180_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1179_j)));
          }
          _1178_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1178_ctorMatchInner, _1181_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1179_j).Sign == 1) {
            _1176_printRhs = (_1176_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1176_printRhs = (_1176_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1181_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))));
        }
        if (_1177_isNumeric) {
          _1173_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1173_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1178_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1173_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1173_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1178_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1172_ctor).dtor_hasAnyArgs) {
          _1176_printRhs = (_1176_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1176_printRhs = (_1176_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1170_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1170_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1128_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1173_ctorMatch), RAST.Expr.create_Block(_1176_printRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _1170_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1170_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1128_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1182_defaultConstrainedTypeParams;
      _1182_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1126_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      RAST._IExpr _1183_printImplBody;
      _1183_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1170_printImplBodyCases);
      Dafny.ISequence<RAST._IModDecl> _1184_printImpl;
      _1184_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1126_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1128_datatypeName), _1125_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1126_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1128_datatypeName), _1125_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1183_printImplBody)))))));
      Dafny.ISequence<RAST._IModDecl> _1185_defaultImpl;
      _1185_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      Dafny.ISequence<RAST._IModDecl> _1186_asRefImpl;
      _1186_asRefImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1187_structName;
        _1187_structName = (RAST.Expr.create_Identifier(_1128_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1188_structAssignments;
        _1188_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi18 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1189_i = BigInteger.Zero; _1189_i < _hi18; _1189_i++) {
          DAST._IDatatypeDtor _1190_dtor;
          _1190_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1189_i);
          _1188_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1188_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1190_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1191_defaultConstrainedTypeParams;
        _1191_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1126_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1192_fullType;
        _1192_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1128_datatypeName), _1125_rTypeParams);
        _1185_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1191_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1192_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1192_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1187_structName, _1188_structAssignments))))))));
        _1186_asRefImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1126_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_1192_fullType), RAST.Type.create_Borrowed(_1192_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self)))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(_1169_enumBody, _1184_printImpl), _1185_defaultImpl), _1186_asRefImpl);
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
        for (BigInteger _1193_i = BigInteger.Zero; _1193_i < _hi19; _1193_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1193_i))));
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
        for (BigInteger _1194_i = BigInteger.Zero; _1194_i < _hi20; _1194_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1194_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding, bool inFn)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger((args).Count)).Sign == 1) {
        BigInteger _1195_i;
        _1195_i = BigInteger.Zero;
        while ((_1195_i) < (new BigInteger((args).Count))) {
          RAST._IType _1196_genTp;
          RAST._IType _out64;
          _out64 = (this).GenType((args).Select(_1195_i), inBinding, inFn);
          _1196_genTp = _out64;
          s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1196_genTp));
          _1195_i = (_1195_i) + (BigInteger.One);
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
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1197_p = _source49.dtor_Path_a0;
          Dafny.ISequence<DAST._IType> _1198_args = _source49.dtor_typeArgs;
          DAST._IResolvedType _1199_resolved = _source49.dtor_resolved;
          unmatched49 = false;
          {
            RAST._IType _1200_t;
            RAST._IType _out65;
            _out65 = DCOMP.COMP.GenPath(_1197_p);
            _1200_t = _out65;
            Dafny.ISequence<RAST._IType> _1201_typeArgs;
            Dafny.ISequence<RAST._IType> _out66;
            _out66 = (this).GenTypeArgs(_1198_args, inBinding, inFn);
            _1201_typeArgs = _out66;
            s = RAST.Type.create_TypeApp(_1200_t, _1201_typeArgs);
            DAST._IResolvedType _source50 = _1199_resolved;
            bool unmatched50 = true;
            if (unmatched50) {
              if (_source50.is_Datatype) {
                DAST._IDatatypeType datatypeType0 = _source50.dtor_datatypeType;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1202___v47 = datatypeType0.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1203_attributes = datatypeType0.dtor_attributes;
                unmatched50 = false;
                {
                  if ((this).IsRcWrapped(_1203_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched50) {
              if (_source50.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1204___v48 = _source50.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1205___v49 = _source50.dtor_attributes;
                unmatched50 = false;
                {
                  if ((_1197_p).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
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
              DAST._IType _1206_t = _source50.dtor_baseType;
              DAST._INewtypeRange _1207_range = _source50.dtor_range;
              bool _1208_erased = _source50.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1209_attributes = _source50.dtor_attributes;
              unmatched50 = false;
              {
                if (_1208_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source51 = DCOMP.COMP.NewtypeToRustType(_1206_t, _1207_range);
                  bool unmatched51 = true;
                  if (unmatched51) {
                    if (_source51.is_Some) {
                      RAST._IType _1210_v = _source51.dtor_value;
                      unmatched51 = false;
                      s = _1210_v;
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
          DAST._IType _1211_inner = _source49.dtor_Nullable_a0;
          unmatched49 = false;
          {
            RAST._IType _1212_innerExpr;
            RAST._IType _out67;
            _out67 = (this).GenType(_1211_inner, inBinding, inFn);
            _1212_innerExpr = _out67;
            s = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::option::Option")), Dafny.Sequence<RAST._IType>.FromElements(_1212_innerExpr));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1213_types = _source49.dtor_Tuple_a0;
          unmatched49 = false;
          {
            Dafny.ISequence<RAST._IType> _1214_args;
            _1214_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1215_i;
            _1215_i = BigInteger.Zero;
            while ((_1215_i) < (new BigInteger((_1213_types).Count))) {
              RAST._IType _1216_generated;
              RAST._IType _out68;
              _out68 = (this).GenType((_1213_types).Select(_1215_i), inBinding, inFn);
              _1216_generated = _out68;
              _1214_args = Dafny.Sequence<RAST._IType>.Concat(_1214_args, Dafny.Sequence<RAST._IType>.FromElements(_1216_generated));
              _1215_i = (_1215_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1213_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1214_args)) : (RAST.__default.SystemTupleType(_1214_args)));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Array) {
          DAST._IType _1217_element = _source49.dtor_element;
          BigInteger _1218_dims = _source49.dtor_dims;
          unmatched49 = false;
          {
            RAST._IType _1219_elem;
            RAST._IType _out69;
            _out69 = (this).GenType(_1217_element, inBinding, inFn);
            _1219_elem = _out69;
            s = _1219_elem;
            BigInteger _1220_i;
            _1220_i = BigInteger.Zero;
            while ((_1220_i) < (_1218_dims)) {
              s = RAST.__default.Rc(RAST.__default.RefCell(RAST.__default.Vec(s)));
              _1220_i = (_1220_i) + (BigInteger.One);
            }
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Seq) {
          DAST._IType _1221_element = _source49.dtor_element;
          unmatched49 = false;
          {
            RAST._IType _1222_elem;
            RAST._IType _out70;
            _out70 = (this).GenType(_1221_element, inBinding, inFn);
            _1222_elem = _out70;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1222_elem));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Set) {
          DAST._IType _1223_element = _source49.dtor_element;
          unmatched49 = false;
          {
            RAST._IType _1224_elem;
            RAST._IType _out71;
            _out71 = (this).GenType(_1223_element, inBinding, inFn);
            _1224_elem = _out71;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1224_elem));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Multiset) {
          DAST._IType _1225_element = _source49.dtor_element;
          unmatched49 = false;
          {
            RAST._IType _1226_elem;
            RAST._IType _out72;
            _out72 = (this).GenType(_1225_element, inBinding, inFn);
            _1226_elem = _out72;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1226_elem));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Map) {
          DAST._IType _1227_key = _source49.dtor_key;
          DAST._IType _1228_value = _source49.dtor_value;
          unmatched49 = false;
          {
            RAST._IType _1229_keyType;
            RAST._IType _out73;
            _out73 = (this).GenType(_1227_key, inBinding, inFn);
            _1229_keyType = _out73;
            RAST._IType _1230_valueType;
            RAST._IType _out74;
            _out74 = (this).GenType(_1228_value, inBinding, inFn);
            _1230_valueType = _out74;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1229_keyType, _1230_valueType));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_MapBuilder) {
          DAST._IType _1231_key = _source49.dtor_key;
          DAST._IType _1232_value = _source49.dtor_value;
          unmatched49 = false;
          {
            RAST._IType _1233_keyType;
            RAST._IType _out75;
            _out75 = (this).GenType(_1231_key, inBinding, inFn);
            _1233_keyType = _out75;
            RAST._IType _1234_valueType;
            RAST._IType _out76;
            _out76 = (this).GenType(_1232_value, inBinding, inFn);
            _1234_valueType = _out76;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1233_keyType, _1234_valueType));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_SetBuilder) {
          DAST._IType _1235_elem = _source49.dtor_element;
          unmatched49 = false;
          {
            RAST._IType _1236_elemType;
            RAST._IType _out77;
            _out77 = (this).GenType(_1235_elem, inBinding, inFn);
            _1236_elemType = _out77;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1236_elemType));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1237_args = _source49.dtor_args;
          DAST._IType _1238_result = _source49.dtor_result;
          unmatched49 = false;
          {
            Dafny.ISequence<RAST._IType> _1239_argTypes;
            _1239_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1240_i;
            _1240_i = BigInteger.Zero;
            while ((_1240_i) < (new BigInteger((_1237_args).Count))) {
              RAST._IType _1241_generated;
              RAST._IType _out78;
              _out78 = (this).GenType((_1237_args).Select(_1240_i), inBinding, true);
              _1241_generated = _out78;
              _1239_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1239_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1241_generated)));
              _1240_i = (_1240_i) + (BigInteger.One);
            }
            RAST._IType _1242_resultType;
            RAST._IType _out79;
            _out79 = (this).GenType(_1238_result, inBinding, (inFn) || (inBinding));
            _1242_resultType = _out79;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1239_argTypes, _1242_resultType)));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h100 = _source49.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1243_name = _h100;
          unmatched49 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1243_name));
        }
      }
      if (unmatched49) {
        if (_source49.is_Primitive) {
          DAST._IPrimitive _1244_p = _source49.dtor_Primitive_a0;
          unmatched49 = false;
          {
            DAST._IPrimitive _source52 = _1244_p;
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
        Dafny.ISequence<Dafny.Rune> _1245_v = _source49.dtor_Passthrough_a0;
        unmatched49 = false;
        s = RAST.__default.RawType(_1245_v);
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
      for (BigInteger _1246_i = BigInteger.Zero; _1246_i < _hi21; _1246_i++) {
        DAST._IMethod _source53 = (body).Select(_1246_i);
        bool unmatched53 = true;
        if (unmatched53) {
          DAST._IMethod _1247_m = _source53;
          unmatched53 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source54 = (_1247_m).dtor_overridingPath;
            bool unmatched54 = true;
            if (unmatched54) {
              if (_source54.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1248_p = _source54.dtor_value;
                unmatched54 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1249_existing;
                  _1249_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1248_p)) {
                    _1249_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1248_p);
                  }
                  RAST._IImplMember _1250_genMethod;
                  RAST._IImplMember _out80;
                  _out80 = (this).GenMethod(_1247_m, true, enclosingType, enclosingTypeParams);
                  _1250_genMethod = _out80;
                  _1249_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1249_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1250_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1248_p, _1249_existing)));
                }
              }
            }
            if (unmatched54) {
              unmatched54 = false;
              {
                RAST._IImplMember _1251_generated;
                RAST._IImplMember _out81;
                _out81 = (this).GenMethod(_1247_m, forTrait, enclosingType, enclosingTypeParams);
                _1251_generated = _out81;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1251_generated));
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
      for (BigInteger _1252_i = BigInteger.Zero; _1252_i < _hi22; _1252_i++) {
        DAST._IFormal _1253_param;
        _1253_param = (@params).Select(_1252_i);
        RAST._IType _1254_paramType;
        RAST._IType _out82;
        _out82 = (this).GenType((_1253_param).dtor_typ, false, false);
        _1254_paramType = _out82;
        if ((!((_1254_paramType).CanReadWithoutClone())) && (!((_1253_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1254_paramType = RAST.Type.create_Borrowed(_1254_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_1253_param).dtor_name), _1254_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1255_params;
      Dafny.ISequence<RAST._IFormal> _out83;
      _out83 = (this).GenParams((m).dtor_params);
      _1255_params = _out83;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1256_paramNames;
      _1256_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1257_paramTypes;
      _1257_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi23 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1258_paramI = BigInteger.Zero; _1258_paramI < _hi23; _1258_paramI++) {
        DAST._IFormal _1259_dafny__formal;
        _1259_dafny__formal = ((m).dtor_params).Select(_1258_paramI);
        RAST._IFormal _1260_formal;
        _1260_formal = (_1255_params).Select(_1258_paramI);
        Dafny.ISequence<Dafny.Rune> _1261_name;
        _1261_name = (_1260_formal).dtor_name;
        _1256_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1256_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1261_name));
        _1257_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1257_paramTypes, _1261_name, (_1260_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1262_fnName;
      _1262_fnName = DCOMP.__default.escapeName((m).dtor_name);
      Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1263_selfIdentifier;
      _1263_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1264_selfId;
        _1264_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((_1262_fnName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_ctor"))) {
          _1264_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        if (forTrait) {
          RAST._IFormal _1265_selfFormal;
          _1265_selfFormal = RAST.Formal.selfBorrowedMut;
          _1255_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1265_selfFormal), _1255_params);
        } else {
          RAST._IType _1266_tpe;
          RAST._IType _out84;
          _out84 = (this).GenType(enclosingType, false, false);
          _1266_tpe = _out84;
          if (!((_1266_tpe).CanReadWithoutClone())) {
            _1266_tpe = RAST.Type.create_Borrowed(_1266_tpe);
          }
          _1255_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1264_selfId, _1266_tpe)), _1255_params);
        }
        _1263_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1264_selfId);
      }
      Dafny.ISequence<RAST._IType> _1267_retTypeArgs;
      _1267_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1268_typeI;
      _1268_typeI = BigInteger.Zero;
      while ((_1268_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1269_typeExpr;
        RAST._IType _out85;
        _out85 = (this).GenType(((m).dtor_outTypes).Select(_1268_typeI), false, false);
        _1269_typeExpr = _out85;
        _1267_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1267_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1269_typeExpr));
        _1268_typeI = (_1268_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1270_visibility;
      _1270_visibility = RAST.Visibility.create_PUB();
      Dafny.ISequence<DAST._ITypeArgDecl> _1271_typeParamsFiltered;
      _1271_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi24 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1272_typeParamI = BigInteger.Zero; _1272_typeParamI < _hi24; _1272_typeParamI++) {
        DAST._ITypeArgDecl _1273_typeParam;
        _1273_typeParam = ((m).dtor_typeParams).Select(_1272_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1273_typeParam).dtor_name)))) {
          _1271_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1271_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1273_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1274_typeParams;
      _1274_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1271_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi25 = new BigInteger((_1271_typeParamsFiltered).Count);
        for (BigInteger _1275_i = BigInteger.Zero; _1275_i < _hi25; _1275_i++) {
          DAST._IType _1276_typeArg;
          RAST._ITypeParamDecl _1277_rTypeParamDecl;
          DAST._IType _out86;
          RAST._ITypeParamDecl _out87;
          (this).GenTypeParam((_1271_typeParamsFiltered).Select(_1275_i), out _out86, out _out87);
          _1276_typeArg = _out86;
          _1277_rTypeParamDecl = _out87;
          var _pat_let_tv101 = _1277_rTypeParamDecl;
          _1277_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1277_rTypeParamDecl, _pat_let6_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let6_0, _1278_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Dafny.Sequence<RAST._IType>.Concat((_pat_let_tv101).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default")))), _pat_let7_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let7_0, _1279_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1278_dt__update__tmp_h0).dtor_content, _1279_dt__update_hconstraints_h0)))));
          _1274_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1274_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1277_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1280_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1281_env = DCOMP.Environment.Default();
      RAST._IExpr _1282_preBody;
      _1282_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      if ((m).dtor_hasBody) {
        RAST._IExpr _1283_earlyReturn;
        _1283_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source55 = (m).dtor_outVars;
        bool unmatched55 = true;
        if (unmatched55) {
          if (_source55.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1284_outVars = _source55.dtor_value;
            unmatched55 = false;
            {
              Dafny.ISequence<RAST._IExpr> _1285_tupleArgs;
              _1285_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi26 = new BigInteger((_1284_outVars).Count);
              for (BigInteger _1286_outI = BigInteger.Zero; _1286_outI < _hi26; _1286_outI++) {
                Dafny.ISequence<Dafny.Rune> _1287_outVar;
                _1287_outVar = (_1284_outVars).Select(_1286_outI);
                RAST._IType _1288_outType;
                RAST._IType _out88;
                _out88 = (this).GenType(((m).dtor_outTypes).Select(_1286_outI), false, false);
                _1288_outType = _out88;
                Dafny.ISequence<Dafny.Rune> _1289_outName;
                _1289_outName = DCOMP.__default.escapeName((_1287_outVar));
                _1256_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1256_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1289_outName));
                RAST._IType _1290_outMaybeType;
                _1290_outMaybeType = (((_1288_outType).CanReadWithoutClone()) ? (_1288_outType) : (RAST.Type.create_Borrowed(_1288_outType)));
                _1257_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1257_paramTypes, _1289_outName, _1290_outMaybeType);
                RAST._IExpr _1291_outVarReturn;
                DCOMP._IOwnership _1292___v50;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1293___v51;
                RAST._IExpr _out89;
                DCOMP._IOwnership _out90;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out91;
                (this).GenExpr(DAST.Expression.create_Ident((_1287_outVar)), Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1289_outName), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>, RAST._IType>(_1289_outName, _1290_outMaybeType))), DCOMP.Ownership.create_OwnershipOwned(), out _out89, out _out90, out _out91);
                _1291_outVarReturn = _out89;
                _1292___v50 = _out90;
                _1293___v51 = _out91;
                _1285_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1285_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1291_outVarReturn));
              }
              if ((new BigInteger((_1285_tupleArgs).Count)) == (BigInteger.One)) {
                _1283_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1285_tupleArgs).Select(BigInteger.Zero)));
              } else {
                _1283_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1285_tupleArgs)));
              }
            }
          }
        }
        if (unmatched55) {
          unmatched55 = false;
        }
        _1281_env = DCOMP.Environment.create(_1256_paramNames, _1257_paramTypes);
        RAST._IExpr _1294_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1295___v52;
        DCOMP._IEnvironment _1296___v53;
        RAST._IExpr _out92;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out93;
        DCOMP._IEnvironment _out94;
        (this).GenStmts((m).dtor_body, _1263_selfIdentifier, _1281_env, true, _1283_earlyReturn, out _out92, out _out93, out _out94);
        _1294_body = _out92;
        _1295___v52 = _out93;
        _1296___v53 = _out94;
        _1280_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1282_preBody).Then(_1294_body));
      } else {
        _1281_env = DCOMP.Environment.create(_1256_paramNames, _1257_paramTypes);
        _1280_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1270_visibility, RAST.Fn.create(_1262_fnName, _1274_typeParams, _1255_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1267_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1267_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1267_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1280_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1297_declarations;
      _1297_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1298_i;
      _1298_i = BigInteger.Zero;
      newEnv = env;
      while ((_1298_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _1299_stmt;
        _1299_stmt = (stmts).Select(_1298_i);
        RAST._IExpr _1300_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1301_recIdents;
        DCOMP._IEnvironment _1302_newEnv2;
        RAST._IExpr _out95;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out96;
        DCOMP._IEnvironment _out97;
        (this).GenStmt(_1299_stmt, selfIdent, newEnv, (isLast) && ((_1298_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out95, out _out96, out _out97);
        _1300_stmtExpr = _out95;
        _1301_recIdents = _out96;
        _1302_newEnv2 = _out97;
        newEnv = _1302_newEnv2;
        DAST._IStatement _source56 = _1299_stmt;
        bool unmatched56 = true;
        if (unmatched56) {
          if (_source56.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1303_name = _source56.dtor_name;
            DAST._IType _1304___v54 = _source56.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> _1305___v55 = _source56.dtor_maybeValue;
            unmatched56 = false;
            {
              _1297_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1297_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_1303_name)));
            }
          }
        }
        if (unmatched56) {
          DAST._IStatement _1306___v56 = _source56;
          unmatched56 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1301_recIdents, _1297_declarations));
        generated = (generated).Then(_1300_stmtExpr);
        _1298_i = (_1298_i) + (BigInteger.One);
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
          Dafny.ISequence<Dafny.Rune> _1307_id = ident0;
          unmatched57 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1308_idRust;
            _1308_idRust = DCOMP.__default.escapeName(_1307_id);
            if (((env).IsBorrowed(_1308_idRust)) || ((env).IsBorrowedMut(_1308_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1308_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1308_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1308_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched57) {
        if (_source57.is_Select) {
          DAST._IExpression _1309_on = _source57.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1310_field = _source57.dtor_field;
          unmatched57 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1311_fieldName;
            _1311_fieldName = DCOMP.__default.escapeName(_1310_field);
            RAST._IExpr _1312_onExpr;
            DCOMP._IOwnership _1313_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1314_recIdents;
            RAST._IExpr _out98;
            DCOMP._IOwnership _out99;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out100;
            (this).GenExpr(_1309_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out98, out _out99, out _out100);
            _1312_onExpr = _out98;
            _1313_onOwned = _out99;
            _1314_recIdents = _out100;
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*("), (_1312_onExpr)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _1311_fieldName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()) = ")), (rhs)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";")));
            readIdents = _1314_recIdents;
            needsIIFE = true;
          }
        }
      }
      if (unmatched57) {
        DAST._IExpression _1315_on = _source57.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1316_indices = _source57.dtor_indices;
        unmatched57 = false;
        {
          RAST._IExpr _1317_onExpr;
          DCOMP._IOwnership _1318_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1319_recIdents;
          RAST._IExpr _out101;
          DCOMP._IOwnership _out102;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out103;
          (this).GenExpr(_1315_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out101, out _out102, out _out103);
          _1317_onExpr = _out101;
          _1318_onOwned = _out102;
          _1319_recIdents = _out103;
          readIdents = _1319_recIdents;
          Dafny.ISequence<Dafny.Rune> _1320_r;
          _1320_r = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          BigInteger _1321_i;
          _1321_i = BigInteger.Zero;
          while ((_1321_i) < (new BigInteger((_1316_indices).Count))) {
            RAST._IExpr _1322_idx;
            DCOMP._IOwnership _1323___v57;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1324_recIdentsIdx;
            RAST._IExpr _out104;
            DCOMP._IOwnership _out105;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out106;
            (this).GenExpr((_1316_indices).Select(_1321_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out104, out _out105, out _out106);
            _1322_idx = _out104;
            _1323___v57 = _out105;
            _1324_recIdentsIdx = _out106;
            _1320_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1320_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let __idx")), Std.Strings.__default.OfNat(_1321_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = <usize as ::dafny_runtime::NumCast>::from(")), (_1322_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap();\n"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1324_recIdentsIdx);
            _1321_i = (_1321_i) + (BigInteger.One);
          }
          _1320_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1320_r, (_1317_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()"));
          _1321_i = BigInteger.Zero;
          while ((_1321_i) < (new BigInteger((_1316_indices).Count))) {
            _1320_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1320_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[__idx")), Std.Strings.__default.OfNat(_1321_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
            _1321_i = (_1321_i) + (BigInteger.One);
          }
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1320_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), (rhs)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n}")));
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
          Dafny.ISequence<Dafny.Rune> _1325_name = _source58.dtor_name;
          DAST._IType _1326_typ = _source58.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source58.dtor_maybeValue;
          if (maybeValue0.is_Some) {
            DAST._IExpression _1327_expression = maybeValue0.dtor_value;
            unmatched58 = false;
            {
              RAST._IType _1328_tpe;
              RAST._IType _out107;
              _out107 = (this).GenType(_1326_typ, true, false);
              _1328_tpe = _out107;
              RAST._IExpr _1329_expr;
              DCOMP._IOwnership _1330_exprOwnership;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1331_recIdents;
              RAST._IExpr _out108;
              DCOMP._IOwnership _out109;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out110;
              (this).GenExpr(_1327_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out108, out _out109, out _out110);
              _1329_expr = _out108;
              _1330_exprOwnership = _out109;
              _1331_recIdents = _out110;
              readIdents = _1331_recIdents;
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_1325_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1328_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1329_expr));
              newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_1325_name), _1328_tpe);
            }
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1332_name = _source58.dtor_name;
          DAST._IType _1333_typ = _source58.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source58.dtor_maybeValue;
          if (maybeValue1.is_None) {
            unmatched58 = false;
            {
              DAST._IStatement _1334_newStmt;
              _1334_newStmt = DAST.Statement.create_DeclareVar(_1332_name, _1333_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1333_typ)));
              RAST._IExpr _out111;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out112;
              DCOMP._IEnvironment _out113;
              (this).GenStmt(_1334_newStmt, selfIdent, env, isLast, earlyReturn, out _out111, out _out112, out _out113);
              generated = _out111;
              readIdents = _out112;
              newEnv = _out113;
            }
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Assign) {
          DAST._IAssignLhs _1335_lhs = _source58.dtor_lhs;
          DAST._IExpression _1336_expression = _source58.dtor_value;
          unmatched58 = false;
          {
            RAST._IExpr _1337_exprGen;
            DCOMP._IOwnership _1338___v58;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1339_exprIdents;
            RAST._IExpr _out114;
            DCOMP._IOwnership _out115;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
            (this).GenExpr(_1336_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out114, out _out115, out _out116);
            _1337_exprGen = _out114;
            _1338___v58 = _out115;
            _1339_exprIdents = _out116;
            if ((_1335_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1340_rustId;
              _1340_rustId = DCOMP.__default.escapeName(((_1335_lhs).dtor_ident));
              Std.Wrappers._IOption<RAST._IType> _1341_tpe;
              _1341_tpe = (env).GetType(_1340_rustId);
            }
            RAST._IExpr _1342_lhsGen;
            bool _1343_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1344_recIdents;
            DCOMP._IEnvironment _1345_resEnv;
            RAST._IExpr _out117;
            bool _out118;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out119;
            DCOMP._IEnvironment _out120;
            (this).GenAssignLhs(_1335_lhs, _1337_exprGen, selfIdent, env, out _out117, out _out118, out _out119, out _out120);
            _1342_lhsGen = _out117;
            _1343_needsIIFE = _out118;
            _1344_recIdents = _out119;
            _1345_resEnv = _out120;
            generated = _1342_lhsGen;
            newEnv = _1345_resEnv;
            if (_1343_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1344_recIdents, _1339_exprIdents);
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_If) {
          DAST._IExpression _1346_cond = _source58.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1347_thnDafny = _source58.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1348_elsDafny = _source58.dtor_els;
          unmatched58 = false;
          {
            RAST._IExpr _1349_cond;
            DCOMP._IOwnership _1350___v59;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1351_recIdents;
            RAST._IExpr _out121;
            DCOMP._IOwnership _out122;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out123;
            (this).GenExpr(_1346_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out121, out _out122, out _out123);
            _1349_cond = _out121;
            _1350___v59 = _out122;
            _1351_recIdents = _out123;
            Dafny.ISequence<Dafny.Rune> _1352_condString;
            _1352_condString = (_1349_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1351_recIdents;
            RAST._IExpr _1353_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1354_thnIdents;
            DCOMP._IEnvironment _1355_thnEnv;
            RAST._IExpr _out124;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out125;
            DCOMP._IEnvironment _out126;
            (this).GenStmts(_1347_thnDafny, selfIdent, env, isLast, earlyReturn, out _out124, out _out125, out _out126);
            _1353_thn = _out124;
            _1354_thnIdents = _out125;
            _1355_thnEnv = _out126;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1354_thnIdents);
            RAST._IExpr _1356_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1357_elsIdents;
            DCOMP._IEnvironment _1358_elsEnv;
            RAST._IExpr _out127;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out128;
            DCOMP._IEnvironment _out129;
            (this).GenStmts(_1348_elsDafny, selfIdent, env, isLast, earlyReturn, out _out127, out _out128, out _out129);
            _1356_els = _out127;
            _1357_elsIdents = _out128;
            _1358_elsEnv = _out129;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1357_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1349_cond, _1353_thn, _1356_els);
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1359_lbl = _source58.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1360_body = _source58.dtor_body;
          unmatched58 = false;
          {
            RAST._IExpr _1361_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1362_bodyIdents;
            DCOMP._IEnvironment _1363_env2;
            RAST._IExpr _out130;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
            DCOMP._IEnvironment _out132;
            (this).GenStmts(_1360_body, selfIdent, env, isLast, earlyReturn, out _out130, out _out131, out _out132);
            _1361_body = _out130;
            _1362_bodyIdents = _out131;
            _1363_env2 = _out132;
            readIdents = _1362_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1359_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1361_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_While) {
          DAST._IExpression _1364_cond = _source58.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1365_body = _source58.dtor_body;
          unmatched58 = false;
          {
            RAST._IExpr _1366_cond;
            DCOMP._IOwnership _1367___v60;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1368_recIdents;
            RAST._IExpr _out133;
            DCOMP._IOwnership _out134;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
            (this).GenExpr(_1364_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out133, out _out134, out _out135);
            _1366_cond = _out133;
            _1367___v60 = _out134;
            _1368_recIdents = _out135;
            readIdents = _1368_recIdents;
            RAST._IExpr _1369_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1370_bodyIdents;
            DCOMP._IEnvironment _1371_bodyEnv;
            RAST._IExpr _out136;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
            DCOMP._IEnvironment _out138;
            (this).GenStmts(_1365_body, selfIdent, env, false, earlyReturn, out _out136, out _out137, out _out138);
            _1369_bodyExpr = _out136;
            _1370_bodyIdents = _out137;
            _1371_bodyEnv = _out138;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1370_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1366_cond), _1369_bodyExpr);
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1372_boundName = _source58.dtor_boundName;
          DAST._IType _1373_boundType = _source58.dtor_boundType;
          DAST._IExpression _1374_over = _source58.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1375_body = _source58.dtor_body;
          unmatched58 = false;
          {
            RAST._IExpr _1376_over;
            DCOMP._IOwnership _1377___v61;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1378_recIdents;
            RAST._IExpr _out139;
            DCOMP._IOwnership _out140;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out141;
            (this).GenExpr(_1374_over, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out139, out _out140, out _out141);
            _1376_over = _out139;
            _1377___v61 = _out140;
            _1378_recIdents = _out141;
            RAST._IType _1379_boundTpe;
            RAST._IType _out142;
            _out142 = (this).GenType(_1373_boundType, false, false);
            _1379_boundTpe = _out142;
            readIdents = _1378_recIdents;
            Dafny.ISequence<Dafny.Rune> _1380_boundRName;
            _1380_boundRName = DCOMP.__default.escapeName(_1372_boundName);
            RAST._IExpr _1381_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1382_bodyIdents;
            DCOMP._IEnvironment _1383_bodyEnv;
            RAST._IExpr _out143;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
            DCOMP._IEnvironment _out145;
            (this).GenStmts(_1375_body, selfIdent, (env).AddAssigned(_1380_boundRName, _1379_boundTpe), false, earlyReturn, out _out143, out _out144, out _out145);
            _1381_bodyExpr = _out143;
            _1382_bodyIdents = _out144;
            _1383_bodyEnv = _out145;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1382_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1380_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1380_boundRName, _1376_over, _1381_bodyExpr);
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1384_toLabel = _source58.dtor_toLabel;
          unmatched58 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source59 = _1384_toLabel;
            bool unmatched59 = true;
            if (unmatched59) {
              if (_source59.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1385_lbl = _source59.dtor_value;
                unmatched59 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1385_lbl)));
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
          Dafny.ISequence<DAST._IStatement> _1386_body = _source58.dtor_body;
          unmatched58 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
            }
            newEnv = env;
            BigInteger _hi27 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1387_paramI = BigInteger.Zero; _1387_paramI < _hi27; _1387_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1388_param;
              _1388_param = ((env).dtor_names).Select(_1387_paramI);
              RAST._IExpr _1389_paramInit;
              DCOMP._IOwnership _1390___v62;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1391___v63;
              RAST._IExpr _out146;
              DCOMP._IOwnership _out147;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out148;
              (this).GenIdent(_1388_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out146, out _out147, out _out148);
              _1389_paramInit = _out146;
              _1390___v62 = _out147;
              _1391___v63 = _out148;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1388_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1389_paramInit)));
              if (((env).dtor_types).Contains(_1388_param)) {
                RAST._IType _1392_declaredType;
                _1392_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1388_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1388_param, _1392_declaredType);
              }
            }
            RAST._IExpr _1393_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1394_bodyIdents;
            DCOMP._IEnvironment _1395_bodyEnv;
            RAST._IExpr _out149;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out150;
            DCOMP._IEnvironment _out151;
            (this).GenStmts(_1386_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), newEnv, false, earlyReturn, out _out149, out _out150, out _out151);
            _1393_bodyExpr = _out149;
            _1394_bodyIdents = _out150;
            _1395_bodyEnv = _out151;
            readIdents = _1394_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1393_bodyExpr)));
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
          DAST._IExpression _1396_on = _source58.dtor_on;
          DAST._ICallName _1397_name = _source58.dtor_callName;
          Dafny.ISequence<DAST._IType> _1398_typeArgs = _source58.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1399_args = _source58.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1400_maybeOutVars = _source58.dtor_outs;
          unmatched58 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IExpr _1401_onExpr;
            DCOMP._IOwnership _1402___v64;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1403_enclosingIdents;
            RAST._IExpr _out152;
            DCOMP._IOwnership _out153;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out154;
            (this).GenExpr(_1396_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out152, out _out153, out _out154);
            _1401_onExpr = _out152;
            _1402___v64 = _out153;
            _1403_enclosingIdents = _out154;
            Dafny.ISequence<RAST._IType> _1404_typeArgsR;
            _1404_typeArgsR = Dafny.Sequence<RAST._IType>.FromElements();
            if ((new BigInteger((_1398_typeArgs).Count)) >= (BigInteger.One)) {
              BigInteger _1405_typeI;
              _1405_typeI = BigInteger.Zero;
              while ((_1405_typeI) < (new BigInteger((_1398_typeArgs).Count))) {
                RAST._IType _1406_tpe;
                RAST._IType _out155;
                _out155 = (this).GenType((_1398_typeArgs).Select(_1405_typeI), false, false);
                _1406_tpe = _out155;
                _1404_typeArgsR = Dafny.Sequence<RAST._IType>.Concat(_1404_typeArgsR, Dafny.Sequence<RAST._IType>.FromElements(_1406_tpe));
                _1405_typeI = (_1405_typeI) + (BigInteger.One);
              }
            }
            Dafny.ISequence<RAST._IExpr> _1407_argExprs;
            _1407_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi28 = new BigInteger((_1399_args).Count);
            for (BigInteger _1408_i = BigInteger.Zero; _1408_i < _hi28; _1408_i++) {
              DCOMP._IOwnership _1409_argOwnership;
              _1409_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              if (((_1397_name).is_CallName) && ((_1408_i) < (new BigInteger((((_1397_name).dtor_signature)).Count)))) {
                RAST._IType _1410_tpe;
                RAST._IType _out156;
                _out156 = (this).GenType(((((_1397_name).dtor_signature)).Select(_1408_i)).dtor_typ, false, false);
                _1410_tpe = _out156;
                if ((_1410_tpe).CanReadWithoutClone()) {
                  _1409_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
                }
              }
              RAST._IExpr _1411_argExpr;
              DCOMP._IOwnership _1412_ownership;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1413_argIdents;
              RAST._IExpr _out157;
              DCOMP._IOwnership _out158;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out159;
              (this).GenExpr((_1399_args).Select(_1408_i), selfIdent, env, _1409_argOwnership, out _out157, out _out158, out _out159);
              _1411_argExpr = _out157;
              _1412_ownership = _out158;
              _1413_argIdents = _out159;
              _1407_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1407_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1411_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1413_argIdents);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1403_enclosingIdents);
            Dafny.ISequence<Dafny.Rune> _1414_renderedName;
            _1414_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
              DAST._ICallName _source60 = _1397_name;
              bool unmatched60 = true;
              if (unmatched60) {
                if (_source60.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _1415_name = _source60.dtor_name;
                  Std.Wrappers._IOption<DAST._IType> _1416___v65 = _source60.dtor_onType;
                  Dafny.ISequence<DAST._IFormal> _1417___v66 = _source60.dtor_signature;
                  unmatched60 = false;
                  return DCOMP.__default.escapeName(_1415_name);
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
            DAST._IExpression _source61 = _1396_on;
            bool unmatched61 = true;
            if (unmatched61) {
              if (_source61.is_Companion) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1418___v67 = _source61.dtor_Companion_a0;
                unmatched61 = false;
                {
                  _1401_onExpr = (_1401_onExpr).MSel(_1414_renderedName);
                }
              }
            }
            if (unmatched61) {
              DAST._IExpression _1419___v68 = _source61;
              unmatched61 = false;
              {
                _1401_onExpr = (_1401_onExpr).Sel(_1414_renderedName);
              }
            }
            generated = _1401_onExpr;
            if ((new BigInteger((_1404_typeArgsR).Count)).Sign == 1) {
              generated = (generated).ApplyType(_1404_typeArgsR);
            }
            generated = (generated).Apply(_1407_argExprs);
            if (((_1400_maybeOutVars).is_Some) && ((new BigInteger(((_1400_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1420_outVar;
              _1420_outVar = DCOMP.__default.escapeName((((_1400_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
              generated = RAST.__default.AssignVar(_1420_outVar, generated);
            } else if (((_1400_maybeOutVars).is_None) || ((new BigInteger(((_1400_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1421_tmpVar;
              _1421_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1422_tmpId;
              _1422_tmpId = RAST.Expr.create_Identifier(_1421_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1421_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1423_outVars;
              _1423_outVars = (_1400_maybeOutVars).dtor_value;
              BigInteger _hi29 = new BigInteger((_1423_outVars).Count);
              for (BigInteger _1424_outI = BigInteger.Zero; _1424_outI < _hi29; _1424_outI++) {
                Dafny.ISequence<Dafny.Rune> _1425_outVar;
                _1425_outVar = DCOMP.__default.escapeName(((_1423_outVars).Select(_1424_outI)));
                RAST._IExpr _1426_rhs;
                _1426_rhs = (_1422_tmpId).Sel(Std.Strings.__default.OfNat(_1424_outI));
                generated = (generated).Then(RAST.__default.AssignVar(_1425_outVar, _1426_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Return) {
          DAST._IExpression _1427_exprDafny = _source58.dtor_expr;
          unmatched58 = false;
          {
            RAST._IExpr _1428_expr;
            DCOMP._IOwnership _1429___v69;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1430_recIdents;
            RAST._IExpr _out160;
            DCOMP._IOwnership _out161;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out162;
            (this).GenExpr(_1427_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out160, out _out161, out _out162);
            _1428_expr = _out160;
            _1429___v69 = _out161;
            _1430_recIdents = _out162;
            readIdents = _1430_recIdents;
            if (isLast) {
              generated = _1428_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1428_expr));
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
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched58) {
        DAST._IExpression _1431_e = _source58.dtor_Print_a0;
        unmatched58 = false;
        {
          RAST._IExpr _1432_printedExpr;
          DCOMP._IOwnership _1433_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1434_recIdents;
          RAST._IExpr _out163;
          DCOMP._IOwnership _out164;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out165;
          (this).GenExpr(_1431_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out163, out _out164, out _out165);
          _1432_printedExpr = _out163;
          _1433_recOwnership = _out164;
          _1434_recIdents = _out165;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1432_printedExpr)));
          readIdents = _1434_recIdents;
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
        DAST._INewtypeRange _1435___v70 = _source62;
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
            bool _1436_b = _h140.dtor_BoolLiteral_a0;
            unmatched63 = false;
            {
              RAST._IExpr _out170;
              DCOMP._IOwnership _out171;
              DCOMP.COMP.FromOwned(RAST.Expr.create_LiteralBool(_1436_b), expectedOwnership, out _out170, out _out171);
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
            Dafny.ISequence<Dafny.Rune> _1437_i = _h141.dtor_IntLiteral_a0;
            DAST._IType _1438_t = _h141.dtor_IntLiteral_a1;
            unmatched63 = false;
            {
              DAST._IType _source64 = _1438_t;
              bool unmatched64 = true;
              if (unmatched64) {
                if (_source64.is_Primitive) {
                  DAST._IPrimitive _h80 = _source64.dtor_Primitive_a0;
                  if (_h80.is_Int) {
                    unmatched64 = false;
                    {
                      if ((new BigInteger((_1437_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1437_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1437_i, true));
                      }
                    }
                  }
                }
              }
              if (unmatched64) {
                DAST._IType _1439_o = _source64;
                unmatched64 = false;
                {
                  RAST._IType _1440_genType;
                  RAST._IType _out172;
                  _out172 = (this).GenType(_1439_o, false, false);
                  _1440_genType = _out172;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1437_i), _1440_genType);
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
            Dafny.ISequence<Dafny.Rune> _1441_n = _h142.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1442_d = _h142.dtor_DecLiteral_a1;
            DAST._IType _1443_t = _h142.dtor_DecLiteral_a2;
            unmatched63 = false;
            {
              DAST._IType _source65 = _1443_t;
              bool unmatched65 = true;
              if (unmatched65) {
                if (_source65.is_Primitive) {
                  DAST._IPrimitive _h81 = _source65.dtor_Primitive_a0;
                  if (_h81.is_Real) {
                    unmatched65 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1441_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1442_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched65) {
                DAST._IType _1444_o = _source65;
                unmatched65 = false;
                {
                  RAST._IType _1445_genType;
                  RAST._IType _out175;
                  _out175 = (this).GenType(_1444_o, false, false);
                  _1445_genType = _out175;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1441_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1442_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1445_genType);
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
            Dafny.ISequence<Dafny.Rune> _1446_l = _h143.dtor_StringLiteral_a0;
            unmatched63 = false;
            {
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1446_l, false));
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
          if (_h144.is_CharLiteral) {
            Dafny.Rune _1447_c = _h144.dtor_CharLiteral_a0;
            unmatched63 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1447_c).Value)));
              if (!((this).UnicodeChars)) {
                r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              } else {
                r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
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
        DAST._ILiteral _h145 = _source63.dtor_Literal_a0;
        DAST._IType _1448_tpe = _h145.dtor_Null_a0;
        unmatched63 = false;
        {
          RAST._IType _1449_tpeGen;
          RAST._IType _out182;
          _out182 = (this).GenType(_1448_tpe, false, false);
          _1449_tpeGen = _out182;
          r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None")), _1449_tpeGen);
          RAST._IExpr _out183;
          DCOMP._IOwnership _out184;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out183, out _out184);
          r = _out183;
          resultingOwnership = _out184;
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
      DAST._IBinOp _1450_op = _let_tmp_rhs52.dtor_op;
      DAST._IExpression _1451_lExpr = _let_tmp_rhs52.dtor_left;
      DAST._IExpression _1452_rExpr = _let_tmp_rhs52.dtor_right;
      DAST.Format._IBinaryOpFormat _1453_format = _let_tmp_rhs52.dtor_format2;
      bool _1454_becomesLeftCallsRight;
      _1454_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source66 = _1450_op;
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
          DAST._IBinOp _1455___v71 = _source66;
          unmatched66 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1456_becomesRightCallsLeft;
      _1456_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source67 = _1450_op;
        bool unmatched67 = true;
        if (unmatched67) {
          if (_source67.is_In) {
            unmatched67 = false;
            return true;
          }
        }
        if (unmatched67) {
          DAST._IBinOp _1457___v72 = _source67;
          unmatched67 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1458_becomesCallLeftRight;
      _1458_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source68 = _1450_op;
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
          DAST._IBinOp _1459___v73 = _source68;
          unmatched68 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      DCOMP._IOwnership _1460_expectedLeftOwnership;
      _1460_expectedLeftOwnership = ((_1454_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1456_becomesRightCallsLeft) || (_1458_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1461_expectedRightOwnership;
      _1461_expectedRightOwnership = (((_1454_becomesLeftCallsRight) || (_1458_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1456_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1462_left;
      DCOMP._IOwnership _1463___v74;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1464_recIdentsL;
      RAST._IExpr _out185;
      DCOMP._IOwnership _out186;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out187;
      (this).GenExpr(_1451_lExpr, selfIdent, env, _1460_expectedLeftOwnership, out _out185, out _out186, out _out187);
      _1462_left = _out185;
      _1463___v74 = _out186;
      _1464_recIdentsL = _out187;
      RAST._IExpr _1465_right;
      DCOMP._IOwnership _1466___v75;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1467_recIdentsR;
      RAST._IExpr _out188;
      DCOMP._IOwnership _out189;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out190;
      (this).GenExpr(_1452_rExpr, selfIdent, env, _1461_expectedRightOwnership, out _out188, out _out189, out _out190);
      _1465_right = _out188;
      _1466___v75 = _out189;
      _1467_recIdentsR = _out190;
      DAST._IBinOp _source69 = _1450_op;
      bool unmatched69 = true;
      if (unmatched69) {
        if (_source69.is_In) {
          unmatched69 = false;
          {
            r = ((_1465_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1462_left);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_SeqProperPrefix) {
          unmatched69 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1462_left, _1465_right, _1453_format);
        }
      }
      if (unmatched69) {
        if (_source69.is_SeqPrefix) {
          unmatched69 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1462_left, _1465_right, _1453_format);
        }
      }
      if (unmatched69) {
        if (_source69.is_SetMerge) {
          unmatched69 = false;
          {
            r = ((_1462_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1465_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_SetSubtraction) {
          unmatched69 = false;
          {
            r = ((_1462_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1465_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_SetIntersection) {
          unmatched69 = false;
          {
            r = ((_1462_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1465_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_Subset) {
          unmatched69 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1462_left, _1465_right, _1453_format);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_ProperSubset) {
          unmatched69 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1462_left, _1465_right, _1453_format);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_SetDisjoint) {
          unmatched69 = false;
          {
            r = ((_1462_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1465_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_MapMerge) {
          unmatched69 = false;
          {
            r = ((_1462_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1465_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_MapSubtraction) {
          unmatched69 = false;
          {
            r = ((_1462_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1465_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_MultisetMerge) {
          unmatched69 = false;
          {
            r = ((_1462_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1465_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_MultisetSubtraction) {
          unmatched69 = false;
          {
            r = ((_1462_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1465_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_MultisetIntersection) {
          unmatched69 = false;
          {
            r = ((_1462_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1465_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_Submultiset) {
          unmatched69 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1462_left, _1465_right, _1453_format);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_ProperSubmultiset) {
          unmatched69 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1462_left, _1465_right, _1453_format);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_MultisetDisjoint) {
          unmatched69 = false;
          {
            r = ((_1462_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1465_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_Concat) {
          unmatched69 = false;
          {
            r = ((_1462_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1465_right);
          }
        }
      }
      if (unmatched69) {
        DAST._IBinOp _1468___v76 = _source69;
        unmatched69 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1450_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1450_op), _1462_left, _1465_right, _1453_format);
          } else {
            DAST._IBinOp _source70 = _1450_op;
            bool unmatched70 = true;
            if (unmatched70) {
              if (_source70.is_Eq) {
                bool _1469_referential = _source70.dtor_referential;
                bool _1470_nullable = _source70.dtor_nullable;
                unmatched70 = false;
                {
                  if (_1469_referential) {
                    if (_1470_nullable) {
                      r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1462_left, _1465_right));
                    } else {
                      r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1462_left, _1465_right));
                    }
                  } else {
                    r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1462_left, _1465_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                  }
                }
              }
            }
            if (unmatched70) {
              if (_source70.is_EuclidianDiv) {
                unmatched70 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1462_left, _1465_right));
                }
              }
            }
            if (unmatched70) {
              if (_source70.is_EuclidianMod) {
                unmatched70 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1462_left, _1465_right));
                }
              }
            }
            if (unmatched70) {
              Dafny.ISequence<Dafny.Rune> _1471_op = _source70.dtor_Passthrough_a0;
              unmatched70 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1471_op, _1462_left, _1465_right, _1453_format);
              }
            }
          }
        }
      }
      RAST._IExpr _out191;
      DCOMP._IOwnership _out192;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out191, out _out192);
      r = _out191;
      resultingOwnership = _out192;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1464_recIdentsL, _1467_recIdentsR);
      return ;
    }
    public void GenExprConvertFromNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs53 = e;
      DAST._IExpression _1472_expr = _let_tmp_rhs53.dtor_value;
      DAST._IType _1473_fromTpe = _let_tmp_rhs53.dtor_from;
      DAST._IType _1474_toTpe = _let_tmp_rhs53.dtor_typ;
      RAST._IExpr _1475_recursiveGen;
      DCOMP._IOwnership _1476_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1477_recIdents;
      RAST._IExpr _out193;
      DCOMP._IOwnership _out194;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out195;
      (this).GenExpr(_1472_expr, selfIdent, env, expectedOwnership, out _out193, out _out194, out _out195);
      _1475_recursiveGen = _out193;
      _1476_recOwned = _out194;
      _1477_recIdents = _out195;
      r = _1475_recursiveGen;
      if (object.Equals(_1476_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      RAST._IExpr _out196;
      DCOMP._IOwnership _out197;
      DCOMP.COMP.FromOwnership(r, _1476_recOwned, expectedOwnership, out _out196, out _out197);
      r = _out196;
      resultingOwnership = _out197;
      readIdents = _1477_recIdents;
    }
    public void GenExprConvertToNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IExpression _1478_expr = _let_tmp_rhs54.dtor_value;
      DAST._IType _1479_fromTpe = _let_tmp_rhs54.dtor_from;
      DAST._IType _1480_toTpe = _let_tmp_rhs54.dtor_typ;
      RAST._IExpr _1481_recursiveGen;
      DCOMP._IOwnership _1482_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1483_recIdents;
      RAST._IExpr _out198;
      DCOMP._IOwnership _out199;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out200;
      (this).GenExpr(_1478_expr, selfIdent, env, expectedOwnership, out _out198, out _out199, out _out200);
      _1481_recursiveGen = _out198;
      _1482_recOwned = _out199;
      _1483_recIdents = _out200;
      r = _1481_recursiveGen;
      if (object.Equals(_1482_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
      RAST._IExpr _out201;
      DCOMP._IOwnership _out202;
      DCOMP.COMP.FromOwnership(r, _1482_recOwned, expectedOwnership, out _out201, out _out202);
      r = _out201;
      resultingOwnership = _out202;
      readIdents = _1483_recIdents;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _1484_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _1485_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _1486_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _1486_toTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1487___v77 = _let_tmp_rhs56.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _1488___v78 = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      DAST._IType _1489_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _1490_range = _let_tmp_rhs57.dtor_range;
      bool _1491_erase = _let_tmp_rhs57.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1492_attributes = _let_tmp_rhs57.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _1493_nativeToType;
      _1493_nativeToType = DCOMP.COMP.NewtypeToRustType(_1489_b, _1490_range);
      if (object.Equals(_1485_fromTpe, _1489_b)) {
        RAST._IExpr _1494_recursiveGen;
        DCOMP._IOwnership _1495_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1496_recIdents;
        RAST._IExpr _out203;
        DCOMP._IOwnership _out204;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out205;
        (this).GenExpr(_1484_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out203, out _out204, out _out205);
        _1494_recursiveGen = _out203;
        _1495_recOwned = _out204;
        _1496_recIdents = _out205;
        readIdents = _1496_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source71 = _1493_nativeToType;
        bool unmatched71 = true;
        if (unmatched71) {
          if (_source71.is_Some) {
            RAST._IType _1497_v = _source71.dtor_value;
            unmatched71 = false;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1494_recursiveGen, RAST.Expr.create_ExprFromType(_1497_v)));
            RAST._IExpr _out206;
            DCOMP._IOwnership _out207;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out206, out _out207);
            r = _out206;
            resultingOwnership = _out207;
          }
        }
        if (unmatched71) {
          unmatched71 = false;
          if (_1491_erase) {
            r = _1494_recursiveGen;
          } else {
            RAST._IType _1498_rhsType;
            RAST._IType _out208;
            _out208 = (this).GenType(_1486_toTpe, true, false);
            _1498_rhsType = _out208;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1498_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1494_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out209;
          DCOMP._IOwnership _out210;
          DCOMP.COMP.FromOwnership(r, _1495_recOwned, expectedOwnership, out _out209, out _out210);
          r = _out209;
          resultingOwnership = _out210;
        }
      } else {
        RAST._IExpr _out211;
        DCOMP._IOwnership _out212;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out213;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1484_expr, _1485_fromTpe, _1489_b), _1489_b, _1486_toTpe), selfIdent, env, expectedOwnership, out _out211, out _out212, out _out213);
        r = _out211;
        resultingOwnership = _out212;
        readIdents = _out213;
      }
    }
    public void GenExprConvertFromNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs58 = e;
      DAST._IExpression _1499_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _1500_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _1501_toTpe = _let_tmp_rhs58.dtor_typ;
      DAST._IType _let_tmp_rhs59 = _1500_fromTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1502___v79 = _let_tmp_rhs59.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _1503___v80 = _let_tmp_rhs59.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs60 = _let_tmp_rhs59.dtor_resolved;
      DAST._IType _1504_b = _let_tmp_rhs60.dtor_baseType;
      DAST._INewtypeRange _1505_range = _let_tmp_rhs60.dtor_range;
      bool _1506_erase = _let_tmp_rhs60.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1507_attributes = _let_tmp_rhs60.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _1508_nativeFromType;
      _1508_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1504_b, _1505_range);
      if (object.Equals(_1504_b, _1501_toTpe)) {
        RAST._IExpr _1509_recursiveGen;
        DCOMP._IOwnership _1510_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1511_recIdents;
        RAST._IExpr _out214;
        DCOMP._IOwnership _out215;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out216;
        (this).GenExpr(_1499_expr, selfIdent, env, expectedOwnership, out _out214, out _out215, out _out216);
        _1509_recursiveGen = _out214;
        _1510_recOwned = _out215;
        _1511_recIdents = _out216;
        readIdents = _1511_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source72 = _1508_nativeFromType;
        bool unmatched72 = true;
        if (unmatched72) {
          if (_source72.is_Some) {
            RAST._IType _1512_v = _source72.dtor_value;
            unmatched72 = false;
            RAST._IType _1513_toTpeRust;
            RAST._IType _out217;
            _out217 = (this).GenType(_1501_toTpe, false, false);
            _1513_toTpeRust = _out217;
            r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1513_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1509_recursiveGen));
            RAST._IExpr _out218;
            DCOMP._IOwnership _out219;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out218, out _out219);
            r = _out218;
            resultingOwnership = _out219;
          }
        }
        if (unmatched72) {
          unmatched72 = false;
          if (_1506_erase) {
            r = _1509_recursiveGen;
          } else {
            r = (_1509_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out220;
          DCOMP._IOwnership _out221;
          DCOMP.COMP.FromOwnership(r, _1510_recOwned, expectedOwnership, out _out220, out _out221);
          r = _out220;
          resultingOwnership = _out221;
        }
      } else {
        if ((_1508_nativeFromType).is_Some) {
          if (object.Equals(_1501_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1514_recursiveGen;
            DCOMP._IOwnership _1515_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1516_recIdents;
            RAST._IExpr _out222;
            DCOMP._IOwnership _out223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out224;
            (this).GenExpr(_1499_expr, selfIdent, env, expectedOwnership, out _out222, out _out223, out _out224);
            _1514_recursiveGen = _out222;
            _1515_recOwned = _out223;
            _1516_recIdents = _out224;
            RAST._IExpr _out225;
            DCOMP._IOwnership _out226;
            DCOMP.COMP.FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1514_recursiveGen, (this).DafnyCharUnderlying)), _1515_recOwned, expectedOwnership, out _out225, out _out226);
            r = _out225;
            resultingOwnership = _out226;
            readIdents = _1516_recIdents;
            return ;
          }
        }
        RAST._IExpr _out227;
        DCOMP._IOwnership _out228;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out229;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1499_expr, _1500_fromTpe, _1504_b), _1504_b, _1501_toTpe), selfIdent, env, expectedOwnership, out _out227, out _out228, out _out229);
        r = _out227;
        resultingOwnership = _out228;
        readIdents = _out229;
      }
    }
    public void GenExprConvertNotImplemented(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs61 = e;
      DAST._IExpression _1517_expr = _let_tmp_rhs61.dtor_value;
      DAST._IType _1518_fromTpe = _let_tmp_rhs61.dtor_from;
      DAST._IType _1519_toTpe = _let_tmp_rhs61.dtor_typ;
      RAST._IType _1520_fromTpeGen;
      RAST._IType _out230;
      _out230 = (this).GenType(_1518_fromTpe, true, false);
      _1520_fromTpeGen = _out230;
      RAST._IType _1521_toTpeGen;
      RAST._IType _out231;
      _out231 = (this).GenType(_1519_toTpe, true, false);
      _1521_toTpeGen = _out231;
      RAST._IExpr _1522_recursiveGen;
      DCOMP._IOwnership _1523_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1524_recIdents;
      RAST._IExpr _out232;
      DCOMP._IOwnership _out233;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out234;
      (this).GenExpr(_1517_expr, selfIdent, env, expectedOwnership, out _out232, out _out233, out _out234);
      _1522_recursiveGen = _out232;
      _1523_recOwned = _out233;
      _1524_recIdents = _out234;
      Dafny.ISequence<Dafny.Rune> _1525_msg;
      _1525_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1520_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1521_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1525_msg);
      r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1522_recursiveGen)._ToString(DCOMP.__default.IND), _1525_msg));
      RAST._IExpr _out235;
      DCOMP._IOwnership _out236;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out235, out _out236);
      r = _out235;
      resultingOwnership = _out236;
      readIdents = _1524_recIdents;
    }
    public void GenExprConvert(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs62 = e;
      DAST._IExpression _1526_expr = _let_tmp_rhs62.dtor_value;
      DAST._IType _1527_fromTpe = _let_tmp_rhs62.dtor_from;
      DAST._IType _1528_toTpe = _let_tmp_rhs62.dtor_typ;
      if (object.Equals(_1527_fromTpe, _1528_toTpe)) {
        RAST._IExpr _1529_recursiveGen;
        DCOMP._IOwnership _1530_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1531_recIdents;
        RAST._IExpr _out237;
        DCOMP._IOwnership _out238;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out239;
        (this).GenExpr(_1526_expr, selfIdent, env, expectedOwnership, out _out237, out _out238, out _out239);
        _1529_recursiveGen = _out237;
        _1530_recOwned = _out238;
        _1531_recIdents = _out239;
        r = _1529_recursiveGen;
        RAST._IExpr _out240;
        DCOMP._IOwnership _out241;
        DCOMP.COMP.FromOwnership(r, _1530_recOwned, expectedOwnership, out _out240, out _out241);
        r = _out240;
        resultingOwnership = _out241;
        readIdents = _1531_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source73 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1527_fromTpe, _1528_toTpe);
        bool unmatched73 = true;
        if (unmatched73) {
          DAST._IType _01 = _source73.dtor__0;
          if (_01.is_Nullable) {
            DAST._IType _1532___v81 = _01.dtor_Nullable_a0;
            DAST._IType _1533___v82 = _source73.dtor__1;
            unmatched73 = false;
            {
              RAST._IExpr _out242;
              DCOMP._IOwnership _out243;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out244;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out242, out _out243, out _out244);
              r = _out242;
              resultingOwnership = _out243;
              readIdents = _out244;
            }
          }
        }
        if (unmatched73) {
          DAST._IType _1534___v83 = _source73.dtor__0;
          DAST._IType _11 = _source73.dtor__1;
          if (_11.is_Nullable) {
            DAST._IType _1535___v84 = _11.dtor_Nullable_a0;
            unmatched73 = false;
            {
              RAST._IExpr _out245;
              DCOMP._IOwnership _out246;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out247;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out245, out _out246, out _out247);
              r = _out245;
              resultingOwnership = _out246;
              readIdents = _out247;
            }
          }
        }
        if (unmatched73) {
          DAST._IType _1536___v85 = _source73.dtor__0;
          DAST._IType _12 = _source73.dtor__1;
          if (_12.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1537___v86 = _12.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1538___v87 = _12.dtor_typeArgs;
            DAST._IResolvedType resolved1 = _12.dtor_resolved;
            if (resolved1.is_Newtype) {
              DAST._IType _1539_b = resolved1.dtor_baseType;
              DAST._INewtypeRange _1540_range = resolved1.dtor_range;
              bool _1541_erase = resolved1.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1542_attributes = resolved1.dtor_attributes;
              unmatched73 = false;
              {
                RAST._IExpr _out248;
                DCOMP._IOwnership _out249;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out250;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out248, out _out249, out _out250);
                r = _out248;
                resultingOwnership = _out249;
                readIdents = _out250;
              }
            }
          }
        }
        if (unmatched73) {
          DAST._IType _02 = _source73.dtor__0;
          if (_02.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1543___v88 = _02.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1544___v89 = _02.dtor_typeArgs;
            DAST._IResolvedType resolved2 = _02.dtor_resolved;
            if (resolved2.is_Newtype) {
              DAST._IType _1545_b = resolved2.dtor_baseType;
              DAST._INewtypeRange _1546_range = resolved2.dtor_range;
              bool _1547_erase = resolved2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1548_attributes = resolved2.dtor_attributes;
              DAST._IType _1549___v90 = _source73.dtor__1;
              unmatched73 = false;
              {
                RAST._IExpr _out251;
                DCOMP._IOwnership _out252;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out253;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out251, out _out252, out _out253);
                r = _out251;
                resultingOwnership = _out252;
                readIdents = _out253;
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
                    RAST._IExpr _1550_recursiveGen;
                    DCOMP._IOwnership _1551___v91;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1552_recIdents;
                    RAST._IExpr _out254;
                    DCOMP._IOwnership _out255;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out256;
                    (this).GenExpr(_1526_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out254, out _out255, out _out256);
                    _1550_recursiveGen = _out254;
                    _1551___v91 = _out255;
                    _1552_recIdents = _out256;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1550_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out257;
                    DCOMP._IOwnership _out258;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out257, out _out258);
                    r = _out257;
                    resultingOwnership = _out258;
                    readIdents = _1552_recIdents;
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
                    RAST._IExpr _1553_recursiveGen;
                    DCOMP._IOwnership _1554___v92;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1555_recIdents;
                    RAST._IExpr _out259;
                    DCOMP._IOwnership _out260;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out261;
                    (this).GenExpr(_1526_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out259, out _out260, out _out261);
                    _1553_recursiveGen = _out259;
                    _1554___v92 = _out260;
                    _1555_recIdents = _out261;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1553_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out262;
                    DCOMP._IOwnership _out263;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out262, out _out263);
                    r = _out262;
                    resultingOwnership = _out263;
                    readIdents = _1555_recIdents;
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
                Dafny.ISequence<Dafny.Rune> _1556___v93 = _15.dtor_Passthrough_a0;
                unmatched73 = false;
                {
                  RAST._IType _1557_rhsType;
                  RAST._IType _out264;
                  _out264 = (this).GenType(_1528_toTpe, true, false);
                  _1557_rhsType = _out264;
                  RAST._IExpr _1558_recursiveGen;
                  DCOMP._IOwnership _1559___v94;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1560_recIdents;
                  RAST._IExpr _out265;
                  DCOMP._IOwnership _out266;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out267;
                  (this).GenExpr(_1526_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out265, out _out266, out _out267);
                  _1558_recursiveGen = _out265;
                  _1559___v94 = _out266;
                  _1560_recIdents = _out267;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1557_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1558_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out268;
                  DCOMP._IOwnership _out269;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out268, out _out269);
                  r = _out268;
                  resultingOwnership = _out269;
                  readIdents = _1560_recIdents;
                }
              }
            }
          }
        }
        if (unmatched73) {
          DAST._IType _06 = _source73.dtor__0;
          if (_06.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1561___v95 = _06.dtor_Passthrough_a0;
            DAST._IType _16 = _source73.dtor__1;
            if (_16.is_Primitive) {
              DAST._IPrimitive _h87 = _16.dtor_Primitive_a0;
              if (_h87.is_Int) {
                unmatched73 = false;
                {
                  RAST._IType _1562_rhsType;
                  RAST._IType _out270;
                  _out270 = (this).GenType(_1527_fromTpe, true, false);
                  _1562_rhsType = _out270;
                  RAST._IExpr _1563_recursiveGen;
                  DCOMP._IOwnership _1564___v96;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1565_recIdents;
                  RAST._IExpr _out271;
                  DCOMP._IOwnership _out272;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out273;
                  (this).GenExpr(_1526_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out271, out _out272, out _out273);
                  _1563_recursiveGen = _out271;
                  _1564___v96 = _out272;
                  _1565_recIdents = _out273;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::dafny_runtime::BigInt::from("), (_1563_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")}")));
                  RAST._IExpr _out274;
                  DCOMP._IOwnership _out275;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out274, out _out275);
                  r = _out274;
                  resultingOwnership = _out275;
                  readIdents = _1565_recIdents;
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
                    RAST._IType _1566_rhsType;
                    RAST._IType _out276;
                    _out276 = (this).GenType(_1528_toTpe, true, false);
                    _1566_rhsType = _out276;
                    RAST._IExpr _1567_recursiveGen;
                    DCOMP._IOwnership _1568___v97;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1569_recIdents;
                    RAST._IExpr _out277;
                    DCOMP._IOwnership _out278;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out279;
                    (this).GenExpr(_1526_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out277, out _out278, out _out279);
                    _1567_recursiveGen = _out277;
                    _1568___v97 = _out278;
                    _1569_recIdents = _out279;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), (_1567_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()")));
                    RAST._IExpr _out280;
                    DCOMP._IOwnership _out281;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out280, out _out281);
                    r = _out280;
                    resultingOwnership = _out281;
                    readIdents = _1569_recIdents;
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
                    RAST._IType _1570_rhsType;
                    RAST._IType _out282;
                    _out282 = (this).GenType(_1527_fromTpe, true, false);
                    _1570_rhsType = _out282;
                    RAST._IExpr _1571_recursiveGen;
                    DCOMP._IOwnership _1572___v98;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1573_recIdents;
                    RAST._IExpr _out283;
                    DCOMP._IOwnership _out284;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out285;
                    (this).GenExpr(_1526_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out283, out _out284, out _out285);
                    _1571_recursiveGen = _out283;
                    _1572___v98 = _out284;
                    _1573_recIdents = _out285;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1571_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out286;
                    DCOMP._IOwnership _out287;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out286, out _out287);
                    r = _out286;
                    resultingOwnership = _out287;
                    readIdents = _1573_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched73) {
          DAST._IType _09 = _source73.dtor__0;
          if (_09.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1574___v99 = _09.dtor_Passthrough_a0;
            DAST._IType _19 = _source73.dtor__1;
            if (_19.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1575___v100 = _19.dtor_Passthrough_a0;
              unmatched73 = false;
              {
                RAST._IExpr _1576_recursiveGen;
                DCOMP._IOwnership _1577___v101;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1578_recIdents;
                RAST._IExpr _out288;
                DCOMP._IOwnership _out289;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out290;
                (this).GenExpr(_1526_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out288, out _out289, out _out290);
                _1576_recursiveGen = _out288;
                _1577___v101 = _out289;
                _1578_recIdents = _out290;
                RAST._IType _1579_toTpeGen;
                RAST._IType _out291;
                _out291 = (this).GenType(_1528_toTpe, true, false);
                _1579_toTpeGen = _out291;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1576_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1579_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out292;
                DCOMP._IOwnership _out293;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out292, out _out293);
                r = _out292;
                resultingOwnership = _out293;
                readIdents = _1578_recIdents;
              }
            }
          }
        }
        if (unmatched73) {
          _System._ITuple2<DAST._IType, DAST._IType> _1580___v102 = _source73;
          unmatched73 = false;
          {
            RAST._IExpr _out294;
            DCOMP._IOwnership _out295;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out296;
            (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out294, out _out295, out _out296);
            r = _out294;
            resultingOwnership = _out295;
            readIdents = _out296;
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
      Std.Wrappers._IOption<RAST._IType> _1581_tpe;
      _1581_tpe = (env).GetType(rName);
      bool _1582_currentlyBorrowed;
      _1582_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1583_noNeedOfClone;
      _1583_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        r = RAST.__default.BorrowMut(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        if (!(_1583_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1583_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1582_currentlyBorrowed) {
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
          DAST._ILiteral _1584___v103 = _source74.dtor_Literal_a0;
          unmatched74 = false;
          RAST._IExpr _out297;
          DCOMP._IOwnership _out298;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out299;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out297, out _out298, out _out299);
          r = _out297;
          resultingOwnership = _out298;
          readIdents = _out299;
        }
      }
      if (unmatched74) {
        if (_source74.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1585_name = _source74.dtor_Ident_a0;
          unmatched74 = false;
          {
            RAST._IExpr _out300;
            DCOMP._IOwnership _out301;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out302;
            (this).GenIdent(DCOMP.__default.escapeName(_1585_name), selfIdent, env, expectedOwnership, out _out300, out _out301, out _out302);
            r = _out300;
            resultingOwnership = _out301;
            readIdents = _out302;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1586_path = _source74.dtor_Companion_a0;
          unmatched74 = false;
          {
            RAST._IExpr _out303;
            _out303 = DCOMP.COMP.GenPathExpr(_1586_path);
            r = _out303;
            if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else {
              RAST._IExpr _out304;
              DCOMP._IOwnership _out305;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out304, out _out305);
              r = _out304;
              resultingOwnership = _out305;
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_InitializationValue) {
          DAST._IType _1587_typ = _source74.dtor_typ;
          unmatched74 = false;
          {
            RAST._IType _1588_typExpr;
            RAST._IType _out306;
            _out306 = (this).GenType(_1587_typ, false, false);
            _1588_typExpr = _out306;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1588_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
            RAST._IExpr _out307;
            DCOMP._IOwnership _out308;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out307, out _out308);
            r = _out307;
            resultingOwnership = _out308;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _1589_values = _source74.dtor_Tuple_a0;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1590_exprs;
            _1590_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi30 = new BigInteger((_1589_values).Count);
            for (BigInteger _1591_i = BigInteger.Zero; _1591_i < _hi30; _1591_i++) {
              RAST._IExpr _1592_recursiveGen;
              DCOMP._IOwnership _1593___v104;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1594_recIdents;
              RAST._IExpr _out309;
              DCOMP._IOwnership _out310;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out311;
              (this).GenExpr((_1589_values).Select(_1591_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out309, out _out310, out _out311);
              _1592_recursiveGen = _out309;
              _1593___v104 = _out310;
              _1594_recIdents = _out311;
              _1590_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1590_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1592_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1594_recIdents);
            }
            r = (((new BigInteger((_1589_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_1590_exprs)) : (RAST.__default.SystemTuple(_1590_exprs)));
            RAST._IExpr _out312;
            DCOMP._IOwnership _out313;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out312, out _out313);
            r = _out312;
            resultingOwnership = _out313;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1595_path = _source74.dtor_path;
          Dafny.ISequence<DAST._IType> _1596_typeArgs = _source74.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1597_args = _source74.dtor_args;
          unmatched74 = false;
          {
            RAST._IExpr _out314;
            _out314 = DCOMP.COMP.GenPathExpr(_1595_path);
            r = _out314;
            if ((new BigInteger((_1596_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1598_typeExprs;
              _1598_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi31 = new BigInteger((_1596_typeArgs).Count);
              for (BigInteger _1599_i = BigInteger.Zero; _1599_i < _hi31; _1599_i++) {
                RAST._IType _1600_typeExpr;
                RAST._IType _out315;
                _out315 = (this).GenType((_1596_typeArgs).Select(_1599_i), false, false);
                _1600_typeExpr = _out315;
                _1598_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1598_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1600_typeExpr));
              }
              r = (r).ApplyType(_1598_typeExprs);
            }
            r = (r).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1601_arguments;
            _1601_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi32 = new BigInteger((_1597_args).Count);
            for (BigInteger _1602_i = BigInteger.Zero; _1602_i < _hi32; _1602_i++) {
              RAST._IExpr _1603_recursiveGen;
              DCOMP._IOwnership _1604___v105;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1605_recIdents;
              RAST._IExpr _out316;
              DCOMP._IOwnership _out317;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out318;
              (this).GenExpr((_1597_args).Select(_1602_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out316, out _out317, out _out318);
              _1603_recursiveGen = _out316;
              _1604___v105 = _out317;
              _1605_recIdents = _out318;
              _1601_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1601_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1603_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1605_recIdents);
            }
            r = (r).Apply(_1601_arguments);
            RAST._IExpr _out319;
            DCOMP._IOwnership _out320;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out319, out _out320);
            r = _out319;
            resultingOwnership = _out320;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_NewArray) {
          Dafny.ISequence<DAST._IExpression> _1606_dims = _source74.dtor_dims;
          DAST._IType _1607_typ = _source74.dtor_typ;
          unmatched74 = false;
          {
            BigInteger _1608_i;
            _1608_i = (new BigInteger((_1606_dims).Count)) - (BigInteger.One);
            RAST._IType _1609_genTyp;
            RAST._IType _out321;
            _out321 = (this).GenType(_1607_typ, false, false);
            _1609_genTyp = _out321;
            Dafny.ISequence<Dafny.Rune> _1610_s;
            _1610_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1609_genTyp)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::std::default::Default>::default()"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            while ((_1608_i).Sign != -1) {
              RAST._IExpr _1611_recursiveGen;
              DCOMP._IOwnership _1612___v106;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1613_recIdents;
              RAST._IExpr _out322;
              DCOMP._IOwnership _out323;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out324;
              (this).GenExpr((_1606_dims).Select(_1608_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out322, out _out323, out _out324);
              _1611_recursiveGen = _out322;
              _1612___v106 = _out323;
              _1613_recIdents = _out324;
              _1610_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), _1610_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), (_1611_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1613_recIdents);
              _1608_i = (_1608_i) - (BigInteger.One);
            }
            r = RAST.Expr.create_RawExpr(_1610_s);
            RAST._IExpr _out325;
            DCOMP._IOwnership _out326;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out325, out _out326);
            r = _out325;
            resultingOwnership = _out326;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_DatatypeValue) {
          DAST._IDatatypeType _1614_datatypeType = _source74.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1615_typeArgs = _source74.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1616_variant = _source74.dtor_variant;
          bool _1617_isCo = _source74.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1618_values = _source74.dtor_contents;
          unmatched74 = false;
          {
            RAST._IExpr _out327;
            _out327 = DCOMP.COMP.GenPathExpr((_1614_datatypeType).dtor_path);
            r = _out327;
            Dafny.ISequence<RAST._IType> _1619_genTypeArgs;
            _1619_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi33 = new BigInteger((_1615_typeArgs).Count);
            for (BigInteger _1620_i = BigInteger.Zero; _1620_i < _hi33; _1620_i++) {
              RAST._IType _1621_typeExpr;
              RAST._IType _out328;
              _out328 = (this).GenType((_1615_typeArgs).Select(_1620_i), false, false);
              _1621_typeExpr = _out328;
              _1619_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1619_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1621_typeExpr));
            }
            if ((new BigInteger((_1615_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1619_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1616_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1622_assignments;
            _1622_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi34 = new BigInteger((_1618_values).Count);
            for (BigInteger _1623_i = BigInteger.Zero; _1623_i < _hi34; _1623_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs63 = (_1618_values).Select(_1623_i);
              Dafny.ISequence<Dafny.Rune> _1624_name = _let_tmp_rhs63.dtor__0;
              DAST._IExpression _1625_value = _let_tmp_rhs63.dtor__1;
              if (_1617_isCo) {
                RAST._IExpr _1626_recursiveGen;
                DCOMP._IOwnership _1627___v107;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1628_recIdents;
                RAST._IExpr _out329;
                DCOMP._IOwnership _out330;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
                (this).GenExpr(_1625_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out329, out _out330, out _out331);
                _1626_recursiveGen = _out329;
                _1627___v107 = _out330;
                _1628_recIdents = _out331;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1628_recIdents);
                Dafny.ISequence<Dafny.Rune> _1629_allReadCloned;
                _1629_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1628_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1630_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1628_recIdents).Elements) {
                    _1630_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1628_recIdents).Contains(_1630_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 3246)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1629_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1629_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1630_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1630_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1628_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1628_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1630_next));
                }
                Dafny.ISequence<Dafny.Rune> _1631_wasAssigned;
                _1631_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1629_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1626_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1622_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1622_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1624_name, RAST.Expr.create_RawExpr(_1631_wasAssigned))));
              } else {
                RAST._IExpr _1632_recursiveGen;
                DCOMP._IOwnership _1633___v108;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1634_recIdents;
                RAST._IExpr _out332;
                DCOMP._IOwnership _out333;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out334;
                (this).GenExpr(_1625_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out332, out _out333, out _out334);
                _1632_recursiveGen = _out332;
                _1633___v108 = _out333;
                _1634_recIdents = _out334;
                _1622_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1622_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1624_name, _1632_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1634_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1622_assignments);
            if ((this).IsRcWrapped((_1614_datatypeType).dtor_attributes)) {
              r = RAST.__default.RcNew(r);
            }
            RAST._IExpr _out335;
            DCOMP._IOwnership _out336;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out335, out _out336);
            r = _out335;
            resultingOwnership = _out336;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Convert) {
          DAST._IExpression _1635___v109 = _source74.dtor_value;
          DAST._IType _1636___v110 = _source74.dtor_from;
          DAST._IType _1637___v111 = _source74.dtor_typ;
          unmatched74 = false;
          {
            RAST._IExpr _out337;
            DCOMP._IOwnership _out338;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out339;
            (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out337, out _out338, out _out339);
            r = _out337;
            resultingOwnership = _out338;
            readIdents = _out339;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SeqConstruct) {
          DAST._IExpression _1638_length = _source74.dtor_length;
          DAST._IExpression _1639_expr = _source74.dtor_elem;
          unmatched74 = false;
          {
            RAST._IExpr _1640_recursiveGen;
            DCOMP._IOwnership _1641___v112;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1642_recIdents;
            RAST._IExpr _out340;
            DCOMP._IOwnership _out341;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out342;
            (this).GenExpr(_1639_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out340, out _out341, out _out342);
            _1640_recursiveGen = _out340;
            _1641___v112 = _out341;
            _1642_recIdents = _out342;
            RAST._IExpr _1643_lengthGen;
            DCOMP._IOwnership _1644___v113;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1645_lengthIdents;
            RAST._IExpr _out343;
            DCOMP._IOwnership _out344;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out345;
            (this).GenExpr(_1638_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out343, out _out344, out _out345);
            _1643_lengthGen = _out343;
            _1644___v113 = _out344;
            _1645_lengthIdents = _out345;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1640_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1643_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1642_recIdents, _1645_lengthIdents);
            RAST._IExpr _out346;
            DCOMP._IOwnership _out347;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out346, out _out347);
            r = _out346;
            resultingOwnership = _out347;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _1646_exprs = _source74.dtor_elements;
          DAST._IType _1647_typ = _source74.dtor_typ;
          unmatched74 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1648_genTpe;
            RAST._IType _out348;
            _out348 = (this).GenType(_1647_typ, false, false);
            _1648_genTpe = _out348;
            BigInteger _1649_i;
            _1649_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1650_args;
            _1650_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1649_i) < (new BigInteger((_1646_exprs).Count))) {
              RAST._IExpr _1651_recursiveGen;
              DCOMP._IOwnership _1652___v114;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1653_recIdents;
              RAST._IExpr _out349;
              DCOMP._IOwnership _out350;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out351;
              (this).GenExpr((_1646_exprs).Select(_1649_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out349, out _out350, out _out351);
              _1651_recursiveGen = _out349;
              _1652___v114 = _out350;
              _1653_recIdents = _out351;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1653_recIdents);
              _1650_args = Dafny.Sequence<RAST._IExpr>.Concat(_1650_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1651_recursiveGen));
              _1649_i = (_1649_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_1650_args);
            if ((new BigInteger((_1650_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1648_genTpe));
            }
            RAST._IExpr _out352;
            DCOMP._IOwnership _out353;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out352, out _out353);
            r = _out352;
            resultingOwnership = _out353;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _1654_exprs = _source74.dtor_elements;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1655_generatedValues;
            _1655_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1656_i;
            _1656_i = BigInteger.Zero;
            while ((_1656_i) < (new BigInteger((_1654_exprs).Count))) {
              RAST._IExpr _1657_recursiveGen;
              DCOMP._IOwnership _1658___v115;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1659_recIdents;
              RAST._IExpr _out354;
              DCOMP._IOwnership _out355;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out356;
              (this).GenExpr((_1654_exprs).Select(_1656_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out354, out _out355, out _out356);
              _1657_recursiveGen = _out354;
              _1658___v115 = _out355;
              _1659_recIdents = _out356;
              _1655_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1655_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1657_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1659_recIdents);
              _1656_i = (_1656_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_1655_generatedValues);
            RAST._IExpr _out357;
            DCOMP._IOwnership _out358;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out357, out _out358);
            r = _out357;
            resultingOwnership = _out358;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _1660_exprs = _source74.dtor_elements;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1661_generatedValues;
            _1661_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1662_i;
            _1662_i = BigInteger.Zero;
            while ((_1662_i) < (new BigInteger((_1660_exprs).Count))) {
              RAST._IExpr _1663_recursiveGen;
              DCOMP._IOwnership _1664___v116;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1665_recIdents;
              RAST._IExpr _out359;
              DCOMP._IOwnership _out360;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out361;
              (this).GenExpr((_1660_exprs).Select(_1662_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out359, out _out360, out _out361);
              _1663_recursiveGen = _out359;
              _1664___v116 = _out360;
              _1665_recIdents = _out361;
              _1661_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1661_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1663_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1665_recIdents);
              _1662_i = (_1662_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_1661_generatedValues);
            RAST._IExpr _out362;
            DCOMP._IOwnership _out363;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out362, out _out363);
            r = _out362;
            resultingOwnership = _out363;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_ToMultiset) {
          DAST._IExpression _1666_expr = _source74.dtor_ToMultiset_a0;
          unmatched74 = false;
          {
            RAST._IExpr _1667_recursiveGen;
            DCOMP._IOwnership _1668___v117;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1669_recIdents;
            RAST._IExpr _out364;
            DCOMP._IOwnership _out365;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out366;
            (this).GenExpr(_1666_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out364, out _out365, out _out366);
            _1667_recursiveGen = _out364;
            _1668___v117 = _out365;
            _1669_recIdents = _out366;
            r = ((_1667_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _1669_recIdents;
            RAST._IExpr _out367;
            DCOMP._IOwnership _out368;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out367, out _out368);
            r = _out367;
            resultingOwnership = _out368;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1670_mapElems = _source74.dtor_mapElems;
          unmatched74 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1671_generatedValues;
            _1671_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1672_i;
            _1672_i = BigInteger.Zero;
            while ((_1672_i) < (new BigInteger((_1670_mapElems).Count))) {
              RAST._IExpr _1673_recursiveGenKey;
              DCOMP._IOwnership _1674___v118;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1675_recIdentsKey;
              RAST._IExpr _out369;
              DCOMP._IOwnership _out370;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out371;
              (this).GenExpr(((_1670_mapElems).Select(_1672_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out369, out _out370, out _out371);
              _1673_recursiveGenKey = _out369;
              _1674___v118 = _out370;
              _1675_recIdentsKey = _out371;
              RAST._IExpr _1676_recursiveGenValue;
              DCOMP._IOwnership _1677___v119;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1678_recIdentsValue;
              RAST._IExpr _out372;
              DCOMP._IOwnership _out373;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out374;
              (this).GenExpr(((_1670_mapElems).Select(_1672_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out372, out _out373, out _out374);
              _1676_recursiveGenValue = _out372;
              _1677___v119 = _out373;
              _1678_recIdentsValue = _out374;
              _1671_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1671_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1673_recursiveGenKey, _1676_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1675_recIdentsKey), _1678_recIdentsValue);
              _1672_i = (_1672_i) + (BigInteger.One);
            }
            _1672_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1679_arguments;
            _1679_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1672_i) < (new BigInteger((_1671_generatedValues).Count))) {
              RAST._IExpr _1680_genKey;
              _1680_genKey = ((_1671_generatedValues).Select(_1672_i)).dtor__0;
              RAST._IExpr _1681_genValue;
              _1681_genValue = ((_1671_generatedValues).Select(_1672_i)).dtor__1;
              _1679_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1679_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1680_genKey, _1681_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _1672_i = (_1672_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_1679_arguments);
            RAST._IExpr _out375;
            DCOMP._IOwnership _out376;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out375, out _out376);
            r = _out375;
            resultingOwnership = _out376;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SeqUpdate) {
          DAST._IExpression _1682_expr = _source74.dtor_expr;
          DAST._IExpression _1683_index = _source74.dtor_indexExpr;
          DAST._IExpression _1684_value = _source74.dtor_value;
          unmatched74 = false;
          {
            RAST._IExpr _1685_exprR;
            DCOMP._IOwnership _1686___v120;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1687_exprIdents;
            RAST._IExpr _out377;
            DCOMP._IOwnership _out378;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out379;
            (this).GenExpr(_1682_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out377, out _out378, out _out379);
            _1685_exprR = _out377;
            _1686___v120 = _out378;
            _1687_exprIdents = _out379;
            RAST._IExpr _1688_indexR;
            DCOMP._IOwnership _1689_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1690_indexIdents;
            RAST._IExpr _out380;
            DCOMP._IOwnership _out381;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out382;
            (this).GenExpr(_1683_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out380, out _out381, out _out382);
            _1688_indexR = _out380;
            _1689_indexOwnership = _out381;
            _1690_indexIdents = _out382;
            RAST._IExpr _1691_valueR;
            DCOMP._IOwnership _1692_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1693_valueIdents;
            RAST._IExpr _out383;
            DCOMP._IOwnership _out384;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out385;
            (this).GenExpr(_1684_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out383, out _out384, out _out385);
            _1691_valueR = _out383;
            _1692_valueOwnership = _out384;
            _1693_valueIdents = _out385;
            r = ((_1685_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1688_indexR, _1691_valueR));
            RAST._IExpr _out386;
            DCOMP._IOwnership _out387;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out386, out _out387);
            r = _out386;
            resultingOwnership = _out387;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1687_exprIdents, _1690_indexIdents), _1693_valueIdents);
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MapUpdate) {
          DAST._IExpression _1694_expr = _source74.dtor_expr;
          DAST._IExpression _1695_index = _source74.dtor_indexExpr;
          DAST._IExpression _1696_value = _source74.dtor_value;
          unmatched74 = false;
          {
            RAST._IExpr _1697_exprR;
            DCOMP._IOwnership _1698___v121;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1699_exprIdents;
            RAST._IExpr _out388;
            DCOMP._IOwnership _out389;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out390;
            (this).GenExpr(_1694_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out388, out _out389, out _out390);
            _1697_exprR = _out388;
            _1698___v121 = _out389;
            _1699_exprIdents = _out390;
            RAST._IExpr _1700_indexR;
            DCOMP._IOwnership _1701_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1702_indexIdents;
            RAST._IExpr _out391;
            DCOMP._IOwnership _out392;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out393;
            (this).GenExpr(_1695_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out391, out _out392, out _out393);
            _1700_indexR = _out391;
            _1701_indexOwnership = _out392;
            _1702_indexIdents = _out393;
            RAST._IExpr _1703_valueR;
            DCOMP._IOwnership _1704_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1705_valueIdents;
            RAST._IExpr _out394;
            DCOMP._IOwnership _out395;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out396;
            (this).GenExpr(_1696_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out394, out _out395, out _out396);
            _1703_valueR = _out394;
            _1704_valueOwnership = _out395;
            _1705_valueIdents = _out396;
            r = ((_1697_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1700_indexR, _1703_valueR));
            RAST._IExpr _out397;
            DCOMP._IOwnership _out398;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out397, out _out398);
            r = _out397;
            resultingOwnership = _out398;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1699_exprIdents, _1702_indexIdents), _1705_valueIdents);
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
                Dafny.ISequence<Dafny.Rune> _1706_id = _source75.dtor_value;
                unmatched75 = false;
                {
                  r = RAST.Expr.create_Identifier(_1706_id);
                  if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
                    r = RAST.__default.Clone(r);
                    resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
                  } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
                    r = RAST.__default.BoxNew(RAST.__default.Clone(r));
                    resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
                  } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
                    if (!(_1706_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                      r = RAST.__default.Borrow(r);
                    }
                    resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
                  } else {
                    if (!(_1706_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                      r = RAST.__default.BorrowMut(r);
                    }
                    resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
                  }
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1706_id);
                }
              }
            }
            if (unmatched75) {
              unmatched75 = false;
              {
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")"));
                RAST._IExpr _out399;
                DCOMP._IOwnership _out400;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out399, out _out400);
                r = _out399;
                resultingOwnership = _out400;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              }
            }
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Ite) {
          DAST._IExpression _1707_cond = _source74.dtor_cond;
          DAST._IExpression _1708_t = _source74.dtor_thn;
          DAST._IExpression _1709_f = _source74.dtor_els;
          unmatched74 = false;
          {
            RAST._IExpr _1710_cond;
            DCOMP._IOwnership _1711___v122;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1712_recIdentsCond;
            RAST._IExpr _out401;
            DCOMP._IOwnership _out402;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
            (this).GenExpr(_1707_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out401, out _out402, out _out403);
            _1710_cond = _out401;
            _1711___v122 = _out402;
            _1712_recIdentsCond = _out403;
            Dafny.ISequence<Dafny.Rune> _1713_condString;
            _1713_condString = (_1710_cond)._ToString(DCOMP.__default.IND);
            RAST._IExpr _1714___v123;
            DCOMP._IOwnership _1715_tHasToBeOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1716___v124;
            RAST._IExpr _out404;
            DCOMP._IOwnership _out405;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out406;
            (this).GenExpr(_1708_t, selfIdent, env, expectedOwnership, out _out404, out _out405, out _out406);
            _1714___v123 = _out404;
            _1715_tHasToBeOwned = _out405;
            _1716___v124 = _out406;
            RAST._IExpr _1717_fExpr;
            DCOMP._IOwnership _1718_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1719_recIdentsF;
            RAST._IExpr _out407;
            DCOMP._IOwnership _out408;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
            (this).GenExpr(_1709_f, selfIdent, env, _1715_tHasToBeOwned, out _out407, out _out408, out _out409);
            _1717_fExpr = _out407;
            _1718_fOwned = _out408;
            _1719_recIdentsF = _out409;
            Dafny.ISequence<Dafny.Rune> _1720_fString;
            _1720_fString = (_1717_fExpr)._ToString(DCOMP.__default.IND);
            RAST._IExpr _1721_tExpr;
            DCOMP._IOwnership _1722___v125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1723_recIdentsT;
            RAST._IExpr _out410;
            DCOMP._IOwnership _out411;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out412;
            (this).GenExpr(_1708_t, selfIdent, env, _1718_fOwned, out _out410, out _out411, out _out412);
            _1721_tExpr = _out410;
            _1722___v125 = _out411;
            _1723_recIdentsT = _out412;
            Dafny.ISequence<Dafny.Rune> _1724_tString;
            _1724_tString = (_1721_tExpr)._ToString(DCOMP.__default.IND);
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _1713_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _1724_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _1720_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})")));
            RAST._IExpr _out413;
            DCOMP._IOwnership _out414;
            DCOMP.COMP.FromOwnership(r, _1718_fOwned, expectedOwnership, out _out413, out _out414);
            r = _out413;
            resultingOwnership = _out414;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1712_recIdentsCond, _1723_recIdentsT), _1719_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source74.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _1725_e = _source74.dtor_expr;
            DAST.Format._IUnaryOpFormat _1726_format = _source74.dtor_format1;
            unmatched74 = false;
            {
              RAST._IExpr _1727_recursiveGen;
              DCOMP._IOwnership _1728___v126;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1729_recIdents;
              RAST._IExpr _out415;
              DCOMP._IOwnership _out416;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out417;
              (this).GenExpr(_1725_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out415, out _out416, out _out417);
              _1727_recursiveGen = _out415;
              _1728___v126 = _out416;
              _1729_recIdents = _out417;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _1727_recursiveGen, _1726_format);
              RAST._IExpr _out418;
              DCOMP._IOwnership _out419;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out418, out _out419);
              r = _out418;
              resultingOwnership = _out419;
              readIdents = _1729_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source74.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _1730_e = _source74.dtor_expr;
            DAST.Format._IUnaryOpFormat _1731_format = _source74.dtor_format1;
            unmatched74 = false;
            {
              RAST._IExpr _1732_recursiveGen;
              DCOMP._IOwnership _1733___v127;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1734_recIdents;
              RAST._IExpr _out420;
              DCOMP._IOwnership _out421;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out422;
              (this).GenExpr(_1730_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out420, out _out421, out _out422);
              _1732_recursiveGen = _out420;
              _1733___v127 = _out421;
              _1734_recIdents = _out422;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _1732_recursiveGen, _1731_format);
              RAST._IExpr _out423;
              DCOMP._IOwnership _out424;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out423, out _out424);
              r = _out423;
              resultingOwnership = _out424;
              readIdents = _1734_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source74.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _1735_e = _source74.dtor_expr;
            DAST.Format._IUnaryOpFormat _1736_format = _source74.dtor_format1;
            unmatched74 = false;
            {
              RAST._IExpr _1737_recursiveGen;
              DCOMP._IOwnership _1738_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1739_recIdents;
              RAST._IExpr _out425;
              DCOMP._IOwnership _out426;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out427;
              (this).GenExpr(_1735_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out425, out _out426, out _out427);
              _1737_recursiveGen = _out425;
              _1738_recOwned = _out426;
              _1739_recIdents = _out427;
              r = ((_1737_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out428;
              DCOMP._IOwnership _out429;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out428, out _out429);
              r = _out428;
              resultingOwnership = _out429;
              readIdents = _1739_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_BinOp) {
          DAST._IBinOp _1740___v128 = _source74.dtor_op;
          DAST._IExpression _1741___v129 = _source74.dtor_left;
          DAST._IExpression _1742___v130 = _source74.dtor_right;
          DAST.Format._IBinaryOpFormat _1743___v131 = _source74.dtor_format2;
          unmatched74 = false;
          RAST._IExpr _out430;
          DCOMP._IOwnership _out431;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out432;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out430, out _out431, out _out432);
          r = _out430;
          resultingOwnership = _out431;
          readIdents = _out432;
        }
      }
      if (unmatched74) {
        if (_source74.is_ArrayLen) {
          DAST._IExpression _1744_expr = _source74.dtor_expr;
          BigInteger _1745_dim = _source74.dtor_dim;
          unmatched74 = false;
          {
            RAST._IExpr _1746_recursiveGen;
            DCOMP._IOwnership _1747___v132;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1748_recIdents;
            RAST._IExpr _out433;
            DCOMP._IOwnership _out434;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out435;
            (this).GenExpr(_1744_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out433, out _out434, out _out435);
            _1746_recursiveGen = _out433;
            _1747___v132 = _out434;
            _1748_recIdents = _out435;
            if ((_1745_dim).Sign == 0) {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), (_1746_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())")));
            } else {
              Dafny.ISequence<Dafny.Rune> _1749_s;
              _1749_s = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(m.borrow().len())")))._ToString(DCOMP.__default.IND);
              BigInteger _1750_i;
              _1750_i = BigInteger.One;
              while ((_1750_i) < (_1745_dim)) {
                _1749_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("m.borrow().get(0).map(|m| "), _1749_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"));
                _1750_i = (_1750_i) + (BigInteger.One);
              }
              r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_1746_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow().get(0).map(|m| ")), _1749_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"))));
            }
            RAST._IExpr _out436;
            DCOMP._IOwnership _out437;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out436, out _out437);
            r = _out436;
            resultingOwnership = _out437;
            readIdents = _1748_recIdents;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MapKeys) {
          DAST._IExpression _1751_expr = _source74.dtor_expr;
          unmatched74 = false;
          {
            RAST._IExpr _1752_recursiveGen;
            DCOMP._IOwnership _1753___v133;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1754_recIdents;
            RAST._IExpr _out438;
            DCOMP._IOwnership _out439;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out440;
            (this).GenExpr(_1751_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out438, out _out439, out _out440);
            _1752_recursiveGen = _out438;
            _1753___v133 = _out439;
            _1754_recIdents = _out440;
            readIdents = _1754_recIdents;
            r = ((_1752_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out441;
            DCOMP._IOwnership _out442;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out441, out _out442);
            r = _out441;
            resultingOwnership = _out442;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MapValues) {
          DAST._IExpression _1755_expr = _source74.dtor_expr;
          unmatched74 = false;
          {
            RAST._IExpr _1756_recursiveGen;
            DCOMP._IOwnership _1757___v134;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1758_recIdents;
            RAST._IExpr _out443;
            DCOMP._IOwnership _out444;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out445;
            (this).GenExpr(_1755_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out443, out _out444, out _out445);
            _1756_recursiveGen = _out443;
            _1757___v134 = _out444;
            _1758_recIdents = _out445;
            readIdents = _1758_recIdents;
            r = ((_1756_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out446;
            DCOMP._IOwnership _out447;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out446, out _out447);
            r = _out446;
            resultingOwnership = _out447;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SelectFn) {
          DAST._IExpression _1759_on = _source74.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1760_field = _source74.dtor_field;
          bool _1761_isDatatype = _source74.dtor_onDatatype;
          bool _1762_isStatic = _source74.dtor_isStatic;
          BigInteger _1763_arity = _source74.dtor_arity;
          unmatched74 = false;
          {
            RAST._IExpr _1764_onExpr;
            DCOMP._IOwnership _1765_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1766_recIdents;
            RAST._IExpr _out448;
            DCOMP._IOwnership _out449;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out450;
            (this).GenExpr(_1759_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out448, out _out449, out _out450);
            _1764_onExpr = _out448;
            _1765_onOwned = _out449;
            _1766_recIdents = _out450;
            Dafny.ISequence<Dafny.Rune> _1767_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _1768_onString;
            _1768_onString = (_1764_onExpr)._ToString(DCOMP.__default.IND);
            if (_1762_isStatic) {
              _1767_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1768_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_1760_field));
            } else {
              _1767_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _1767_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1767_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _1768_onString), ((object.Equals(_1765_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _1769_args;
              _1769_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _1770_i;
              _1770_i = BigInteger.Zero;
              while ((_1770_i) < (_1763_arity)) {
                if ((_1770_i).Sign == 1) {
                  _1769_args = Dafny.Sequence<Dafny.Rune>.Concat(_1769_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _1769_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1769_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_1770_i));
                _1770_i = (_1770_i) + (BigInteger.One);
              }
              _1767_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1767_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _1769_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _1767_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1767_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_1760_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1769_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _1767_s = Dafny.Sequence<Dafny.Rune>.Concat(_1767_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _1767_s = Dafny.Sequence<Dafny.Rune>.Concat(_1767_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _1771_typeShape;
            _1771_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _1772_i;
            _1772_i = BigInteger.Zero;
            while ((_1772_i) < (_1763_arity)) {
              if ((_1772_i).Sign == 1) {
                _1771_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1771_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _1771_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1771_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _1772_i = (_1772_i) + (BigInteger.One);
            }
            _1771_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1771_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _1767_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _1767_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _1771_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_1767_s);
            RAST._IExpr _out451;
            DCOMP._IOwnership _out452;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out451, out _out452);
            r = _out451;
            resultingOwnership = _out452;
            readIdents = _1766_recIdents;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Select) {
          DAST._IExpression expr0 = _source74.dtor_expr;
          if (expr0.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1773_c = expr0.dtor_Companion_a0;
            Dafny.ISequence<Dafny.Rune> _1774_field = _source74.dtor_field;
            bool _1775_isConstant = _source74.dtor_isConstant;
            bool _1776_isDatatype = _source74.dtor_onDatatype;
            DAST._IType _1777_fieldType = _source74.dtor_fieldType;
            unmatched74 = false;
            {
              RAST._IExpr _1778_onExpr;
              DCOMP._IOwnership _1779_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1780_recIdents;
              RAST._IExpr _out453;
              DCOMP._IOwnership _out454;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out455;
              (this).GenExpr(DAST.Expression.create_Companion(_1773_c), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out453, out _out454, out _out455);
              _1778_onExpr = _out453;
              _1779_onOwned = _out454;
              _1780_recIdents = _out455;
              r = ((_1778_onExpr).MSel(DCOMP.__default.escapeName(_1774_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out456;
              DCOMP._IOwnership _out457;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out456, out _out457);
              r = _out456;
              resultingOwnership = _out457;
              readIdents = _1780_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Select) {
          DAST._IExpression _1781_on = _source74.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1782_field = _source74.dtor_field;
          bool _1783_isConstant = _source74.dtor_isConstant;
          bool _1784_isDatatype = _source74.dtor_onDatatype;
          DAST._IType _1785_fieldType = _source74.dtor_fieldType;
          unmatched74 = false;
          {
            if (_1784_isDatatype) {
              RAST._IExpr _1786_onExpr;
              DCOMP._IOwnership _1787_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1788_recIdents;
              RAST._IExpr _out458;
              DCOMP._IOwnership _out459;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out460;
              (this).GenExpr(_1781_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out458, out _out459, out _out460);
              _1786_onExpr = _out458;
              _1787_onOwned = _out459;
              _1788_recIdents = _out460;
              r = ((_1786_onExpr).Sel(DCOMP.__default.escapeName(_1782_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _1789_typ;
              RAST._IType _out461;
              _out461 = (this).GenType(_1785_fieldType, false, false);
              _1789_typ = _out461;
              RAST._IExpr _out462;
              DCOMP._IOwnership _out463;
              DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out462, out _out463);
              r = _out462;
              resultingOwnership = _out463;
              readIdents = _1788_recIdents;
            } else {
              RAST._IExpr _1790_onExpr;
              DCOMP._IOwnership _1791_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1792_recIdents;
              RAST._IExpr _out464;
              DCOMP._IOwnership _out465;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out466;
              (this).GenExpr(_1781_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out464, out _out465, out _out466);
              _1790_onExpr = _out464;
              _1791_onOwned = _out465;
              _1792_recIdents = _out466;
              r = _1790_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_1782_field));
              if (_1783_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _1793_s;
                _1793_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_1790_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_1782_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_1793_s);
              }
              DCOMP._IOwnership _1794_fromOwnership;
              _1794_fromOwnership = ((_1783_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out467;
              DCOMP._IOwnership _out468;
              DCOMP.COMP.FromOwnership(r, _1794_fromOwnership, expectedOwnership, out _out467, out _out468);
              r = _out467;
              resultingOwnership = _out468;
              readIdents = _1792_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Index) {
          DAST._IExpression _1795_on = _source74.dtor_expr;
          DAST._ICollKind _1796_collKind = _source74.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _1797_indices = _source74.dtor_indices;
          unmatched74 = false;
          {
            RAST._IExpr _1798_onExpr;
            DCOMP._IOwnership _1799_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1800_recIdents;
            RAST._IExpr _out469;
            DCOMP._IOwnership _out470;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out471;
            (this).GenExpr(_1795_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out469, out _out470, out _out471);
            _1798_onExpr = _out469;
            _1799_onOwned = _out470;
            _1800_recIdents = _out471;
            readIdents = _1800_recIdents;
            r = _1798_onExpr;
            BigInteger _1801_i;
            _1801_i = BigInteger.Zero;
            while ((_1801_i) < (new BigInteger((_1797_indices).Count))) {
              if (object.Equals(_1796_collKind, DAST.CollKind.create_Array())) {
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              RAST._IExpr _1802_idx;
              DCOMP._IOwnership _1803_idxOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1804_recIdentsIdx;
              RAST._IExpr _out472;
              DCOMP._IOwnership _out473;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out474;
              (this).GenExpr((_1797_indices).Select(_1801_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out472, out _out473, out _out474);
              _1802_idx = _out472;
              _1803_idxOwned = _out473;
              _1804_recIdentsIdx = _out474;
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_1802_idx);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1804_recIdentsIdx);
              _1801_i = (_1801_i) + (BigInteger.One);
            }
            RAST._IExpr _out475;
            DCOMP._IOwnership _out476;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out475, out _out476);
            r = _out475;
            resultingOwnership = _out476;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_IndexRange) {
          DAST._IExpression _1805_on = _source74.dtor_expr;
          bool _1806_isArray = _source74.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _1807_low = _source74.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _1808_high = _source74.dtor_high;
          unmatched74 = false;
          {
            RAST._IExpr _1809_onExpr;
            DCOMP._IOwnership _1810_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1811_recIdents;
            RAST._IExpr _out477;
            DCOMP._IOwnership _out478;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out479;
            (this).GenExpr(_1805_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out477, out _out478, out _out479);
            _1809_onExpr = _out477;
            _1810_onOwned = _out478;
            _1811_recIdents = _out479;
            readIdents = _1811_recIdents;
            Dafny.ISequence<Dafny.Rune> _1812_methodName;
            _1812_methodName = (((_1807_low).is_Some) ? ((((_1808_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_1808_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _1813_arguments;
            _1813_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source76 = _1807_low;
            bool unmatched76 = true;
            if (unmatched76) {
              if (_source76.is_Some) {
                DAST._IExpression _1814_l = _source76.dtor_value;
                unmatched76 = false;
                {
                  RAST._IExpr _1815_lExpr;
                  DCOMP._IOwnership _1816___v135;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1817_recIdentsL;
                  RAST._IExpr _out480;
                  DCOMP._IOwnership _out481;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out482;
                  (this).GenExpr(_1814_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out480, out _out481, out _out482);
                  _1815_lExpr = _out480;
                  _1816___v135 = _out481;
                  _1817_recIdentsL = _out482;
                  _1813_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1813_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1815_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1817_recIdentsL);
                }
              }
            }
            if (unmatched76) {
              unmatched76 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source77 = _1808_high;
            bool unmatched77 = true;
            if (unmatched77) {
              if (_source77.is_Some) {
                DAST._IExpression _1818_h = _source77.dtor_value;
                unmatched77 = false;
                {
                  RAST._IExpr _1819_hExpr;
                  DCOMP._IOwnership _1820___v136;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1821_recIdentsH;
                  RAST._IExpr _out483;
                  DCOMP._IOwnership _out484;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out485;
                  (this).GenExpr(_1818_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out483, out _out484, out _out485);
                  _1819_hExpr = _out483;
                  _1820___v136 = _out484;
                  _1821_recIdentsH = _out485;
                  _1813_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1813_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1819_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1821_recIdentsH);
                }
              }
            }
            if (unmatched77) {
              unmatched77 = false;
            }
            r = _1809_onExpr;
            if (_1806_isArray) {
              if (!(_1812_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _1812_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1812_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _1812_methodName))).Apply(_1813_arguments);
            } else {
              if (!(_1812_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_1812_methodName)).Apply(_1813_arguments);
              }
            }
            RAST._IExpr _out486;
            DCOMP._IOwnership _out487;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out486, out _out487);
            r = _out486;
            resultingOwnership = _out487;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_TupleSelect) {
          DAST._IExpression _1822_on = _source74.dtor_expr;
          BigInteger _1823_idx = _source74.dtor_index;
          DAST._IType _1824_fieldType = _source74.dtor_fieldType;
          unmatched74 = false;
          {
            RAST._IExpr _1825_onExpr;
            DCOMP._IOwnership _1826_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1827_recIdents;
            RAST._IExpr _out488;
            DCOMP._IOwnership _out489;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out490;
            (this).GenExpr(_1822_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out488, out _out489, out _out490);
            _1825_onExpr = _out488;
            _1826_onOwnership = _out489;
            _1827_recIdents = _out490;
            Dafny.ISequence<Dafny.Rune> _1828_selName;
            _1828_selName = Std.Strings.__default.OfNat(_1823_idx);
            DAST._IType _source78 = _1824_fieldType;
            bool unmatched78 = true;
            if (unmatched78) {
              if (_source78.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1829_tps = _source78.dtor_Tuple_a0;
                unmatched78 = false;
                if (((_1824_fieldType).is_Tuple) && ((new BigInteger((_1829_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _1828_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1828_selName);
                }
              }
            }
            if (unmatched78) {
              DAST._IType _1830___v137 = _source78;
              unmatched78 = false;
            }
            r = (_1825_onExpr).Sel(_1828_selName);
            RAST._IExpr _out491;
            DCOMP._IOwnership _out492;
            DCOMP.COMP.FromOwnership(r, _1826_onOwnership, expectedOwnership, out _out491, out _out492);
            r = _out491;
            resultingOwnership = _out492;
            readIdents = _1827_recIdents;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Call) {
          DAST._IExpression _1831_on = _source74.dtor_on;
          DAST._ICallName _1832_name = _source74.dtor_callName;
          Dafny.ISequence<DAST._IType> _1833_typeArgs = _source74.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1834_args = _source74.dtor_args;
          unmatched74 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IExpr _1835_onExpr;
            DCOMP._IOwnership _1836___v138;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1837_recIdents;
            RAST._IExpr _out493;
            DCOMP._IOwnership _out494;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out495;
            (this).GenExpr(_1831_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out493, out _out494, out _out495);
            _1835_onExpr = _out493;
            _1836___v138 = _out494;
            _1837_recIdents = _out495;
            Dafny.ISequence<RAST._IType> _1838_typeExprs;
            _1838_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
            if ((new BigInteger((_1833_typeArgs).Count)) >= (BigInteger.One)) {
              BigInteger _hi35 = new BigInteger((_1833_typeArgs).Count);
              for (BigInteger _1839_typeI = BigInteger.Zero; _1839_typeI < _hi35; _1839_typeI++) {
                RAST._IType _1840_typeExpr;
                RAST._IType _out496;
                _out496 = (this).GenType((_1833_typeArgs).Select(_1839_typeI), false, false);
                _1840_typeExpr = _out496;
                _1838_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1838_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1840_typeExpr));
              }
            }
            Dafny.ISequence<RAST._IExpr> _1841_argExprs;
            _1841_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi36 = new BigInteger((_1834_args).Count);
            for (BigInteger _1842_i = BigInteger.Zero; _1842_i < _hi36; _1842_i++) {
              DCOMP._IOwnership _1843_argOwnership;
              _1843_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              if (((_1832_name).is_CallName) && ((_1842_i) < (new BigInteger((((_1832_name).dtor_signature)).Count)))) {
                RAST._IType _1844_tpe;
                RAST._IType _out497;
                _out497 = (this).GenType(((((_1832_name).dtor_signature)).Select(_1842_i)).dtor_typ, false, false);
                _1844_tpe = _out497;
                if ((_1844_tpe).CanReadWithoutClone()) {
                  _1843_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
                }
              }
              RAST._IExpr _1845_argExpr;
              DCOMP._IOwnership _1846___v139;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1847_argIdents;
              RAST._IExpr _out498;
              DCOMP._IOwnership _out499;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out500;
              (this).GenExpr((_1834_args).Select(_1842_i), selfIdent, env, _1843_argOwnership, out _out498, out _out499, out _out500);
              _1845_argExpr = _out498;
              _1846___v139 = _out499;
              _1847_argIdents = _out500;
              _1841_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1841_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1845_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1847_argIdents);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1837_recIdents);
            Dafny.ISequence<Dafny.Rune> _1848_renderedName;
            _1848_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
              DAST._ICallName _source79 = _1832_name;
              bool unmatched79 = true;
              if (unmatched79) {
                if (_source79.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _1849_ident = _source79.dtor_name;
                  Std.Wrappers._IOption<DAST._IType> _1850___v140 = _source79.dtor_onType;
                  Dafny.ISequence<DAST._IFormal> _1851___v141 = _source79.dtor_signature;
                  unmatched79 = false;
                  return DCOMP.__default.escapeName(_1849_ident);
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
            DAST._IExpression _source80 = _1831_on;
            bool unmatched80 = true;
            if (unmatched80) {
              if (_source80.is_Companion) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1852___v142 = _source80.dtor_Companion_a0;
                unmatched80 = false;
                {
                  _1835_onExpr = (_1835_onExpr).MSel(_1848_renderedName);
                }
              }
            }
            if (unmatched80) {
              DAST._IExpression _1853___v143 = _source80;
              unmatched80 = false;
              {
                _1835_onExpr = (_1835_onExpr).Sel(_1848_renderedName);
              }
            }
            r = _1835_onExpr;
            if ((new BigInteger((_1838_typeExprs).Count)).Sign == 1) {
              r = (r).ApplyType(_1838_typeExprs);
            }
            r = (r).Apply(_1841_argExprs);
            RAST._IExpr _out501;
            DCOMP._IOwnership _out502;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out501, out _out502);
            r = _out501;
            resultingOwnership = _out502;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _1854_paramsDafny = _source74.dtor_params;
          DAST._IType _1855_retType = _source74.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _1856_body = _source74.dtor_body;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IFormal> _1857_params;
            Dafny.ISequence<RAST._IFormal> _out503;
            _out503 = (this).GenParams(_1854_paramsDafny);
            _1857_params = _out503;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1858_paramNames;
            _1858_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1859_paramTypesMap;
            _1859_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi37 = new BigInteger((_1857_params).Count);
            for (BigInteger _1860_i = BigInteger.Zero; _1860_i < _hi37; _1860_i++) {
              Dafny.ISequence<Dafny.Rune> _1861_name;
              _1861_name = ((_1857_params).Select(_1860_i)).dtor_name;
              _1858_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1858_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1861_name));
              _1859_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1859_paramTypesMap, _1861_name, ((_1857_params).Select(_1860_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _1862_env;
            _1862_env = DCOMP.Environment.create(_1858_paramNames, _1859_paramTypesMap);
            RAST._IExpr _1863_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1864_recIdents;
            DCOMP._IEnvironment _1865___v144;
            RAST._IExpr _out504;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out505;
            DCOMP._IEnvironment _out506;
            (this).GenStmts(_1856_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), _1862_env, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out504, out _out505, out _out506);
            _1863_recursiveGen = _out504;
            _1864_recIdents = _out505;
            _1865___v144 = _out506;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _1864_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1864_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_1866_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll6 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in (_1866_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _1867_name = (Dafny.ISequence<Dafny.Rune>)_compr_6;
                if ((_1866_paramNames).Contains(_1867_name)) {
                  _coll6.Add(_1867_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll6);
            }))())(_1858_paramNames));
            RAST._IExpr _1868_allReadCloned;
            _1868_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_1864_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _1869_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_1864_recIdents).Elements) {
                _1869_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_1864_recIdents).Contains(_1869_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 3710)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) && ((_1869_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
                  _1868_allReadCloned = (_1868_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
                }
              } else if (!((_1858_paramNames).Contains(_1869_next))) {
                _1868_allReadCloned = (_1868_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1869_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.Expr.create_Identifier(_1869_next)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1869_next));
              }
              _1864_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1864_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1869_next));
            }
            RAST._IType _1870_retTypeGen;
            RAST._IType _out507;
            _out507 = (this).GenType(_1855_retType, false, true);
            _1870_retTypeGen = _out507;
            r = RAST.Expr.create_Block((_1868_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_1857_params, Std.Wrappers.Option<RAST._IType>.create_Some(_1870_retTypeGen), RAST.Expr.create_Block(_1863_recursiveGen)))));
            RAST._IExpr _out508;
            DCOMP._IOwnership _out509;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out508, out _out509);
            r = _out508;
            resultingOwnership = _out509;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _1871_values = _source74.dtor_values;
          DAST._IType _1872_retType = _source74.dtor_retType;
          DAST._IExpression _1873_expr = _source74.dtor_expr;
          unmatched74 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1874_paramNames;
            _1874_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _1875_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out510;
            _out510 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_1876_value) => {
              return (_1876_value).dtor__0;
            })), _1871_values));
            _1875_paramFormals = _out510;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1877_paramTypes;
            _1877_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1878_paramNamesSet;
            _1878_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi38 = new BigInteger((_1871_values).Count);
            for (BigInteger _1879_i = BigInteger.Zero; _1879_i < _hi38; _1879_i++) {
              Dafny.ISequence<Dafny.Rune> _1880_name;
              _1880_name = (((_1871_values).Select(_1879_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _1881_rName;
              _1881_rName = DCOMP.__default.escapeName(_1880_name);
              _1874_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1874_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1881_rName));
              _1877_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1877_paramTypes, _1881_rName, ((_1875_paramFormals).Select(_1879_i)).dtor_tpe);
              _1878_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1878_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1881_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi39 = new BigInteger((_1871_values).Count);
            for (BigInteger _1882_i = BigInteger.Zero; _1882_i < _hi39; _1882_i++) {
              RAST._IType _1883_typeGen;
              RAST._IType _out511;
              _out511 = (this).GenType((((_1871_values).Select(_1882_i)).dtor__0).dtor_typ, false, true);
              _1883_typeGen = _out511;
              RAST._IExpr _1884_valueGen;
              DCOMP._IOwnership _1885___v145;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1886_recIdents;
              RAST._IExpr _out512;
              DCOMP._IOwnership _out513;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out514;
              (this).GenExpr(((_1871_values).Select(_1882_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out512, out _out513, out _out514);
              _1884_valueGen = _out512;
              _1885___v145 = _out513;
              _1886_recIdents = _out514;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_1871_values).Select(_1882_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1883_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1884_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1886_recIdents);
            }
            DCOMP._IEnvironment _1887_newEnv;
            _1887_newEnv = DCOMP.Environment.create(_1874_paramNames, _1877_paramTypes);
            RAST._IExpr _1888_recGen;
            DCOMP._IOwnership _1889_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1890_recIdents;
            RAST._IExpr _out515;
            DCOMP._IOwnership _out516;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out517;
            (this).GenExpr(_1873_expr, selfIdent, _1887_newEnv, expectedOwnership, out _out515, out _out516, out _out517);
            _1888_recGen = _out515;
            _1889_recOwned = _out516;
            _1890_recIdents = _out517;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1890_recIdents, _1878_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_1888_recGen));
            RAST._IExpr _out518;
            DCOMP._IOwnership _out519;
            DCOMP.COMP.FromOwnership(r, _1889_recOwned, expectedOwnership, out _out518, out _out519);
            r = _out518;
            resultingOwnership = _out519;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _1891_name = _source74.dtor_name;
          DAST._IType _1892_tpe = _source74.dtor_typ;
          DAST._IExpression _1893_value = _source74.dtor_value;
          DAST._IExpression _1894_iifeBody = _source74.dtor_iifeBody;
          unmatched74 = false;
          {
            RAST._IExpr _1895_valueGen;
            DCOMP._IOwnership _1896___v146;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1897_recIdents;
            RAST._IExpr _out520;
            DCOMP._IOwnership _out521;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out522;
            (this).GenExpr(_1893_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out520, out _out521, out _out522);
            _1895_valueGen = _out520;
            _1896___v146 = _out521;
            _1897_recIdents = _out522;
            readIdents = _1897_recIdents;
            RAST._IType _1898_valueTypeGen;
            RAST._IType _out523;
            _out523 = (this).GenType(_1892_tpe, false, true);
            _1898_valueTypeGen = _out523;
            RAST._IExpr _1899_bodyGen;
            DCOMP._IOwnership _1900___v147;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1901_bodyIdents;
            RAST._IExpr _out524;
            DCOMP._IOwnership _out525;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out526;
            (this).GenExpr(_1894_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out524, out _out525, out _out526);
            _1899_bodyGen = _out524;
            _1900___v147 = _out525;
            _1901_bodyIdents = _out526;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1901_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_1891_name)))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_1891_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_1898_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1895_valueGen))).Then(_1899_bodyGen));
            RAST._IExpr _out527;
            DCOMP._IOwnership _out528;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out527, out _out528);
            r = _out527;
            resultingOwnership = _out528;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Apply) {
          DAST._IExpression _1902_func = _source74.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _1903_args = _source74.dtor_args;
          unmatched74 = false;
          {
            RAST._IExpr _1904_funcExpr;
            DCOMP._IOwnership _1905___v148;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1906_recIdents;
            RAST._IExpr _out529;
            DCOMP._IOwnership _out530;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out531;
            (this).GenExpr(_1902_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out529, out _out530, out _out531);
            _1904_funcExpr = _out529;
            _1905___v148 = _out530;
            _1906_recIdents = _out531;
            readIdents = _1906_recIdents;
            Dafny.ISequence<RAST._IExpr> _1907_rArgs;
            _1907_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi40 = new BigInteger((_1903_args).Count);
            for (BigInteger _1908_i = BigInteger.Zero; _1908_i < _hi40; _1908_i++) {
              RAST._IExpr _1909_argExpr;
              DCOMP._IOwnership _1910_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1911_argIdents;
              RAST._IExpr _out532;
              DCOMP._IOwnership _out533;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out534;
              (this).GenExpr((_1903_args).Select(_1908_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out532, out _out533, out _out534);
              _1909_argExpr = _out532;
              _1910_argOwned = _out533;
              _1911_argIdents = _out534;
              _1907_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1907_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1909_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1911_argIdents);
            }
            r = (_1904_funcExpr).Apply(_1907_rArgs);
            RAST._IExpr _out535;
            DCOMP._IOwnership _out536;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out535, out _out536);
            r = _out535;
            resultingOwnership = _out536;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_TypeTest) {
          DAST._IExpression _1912_on = _source74.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1913_dType = _source74.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _1914_variant = _source74.dtor_variant;
          unmatched74 = false;
          {
            RAST._IExpr _1915_exprGen;
            DCOMP._IOwnership _1916___v149;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1917_recIdents;
            RAST._IExpr _out537;
            DCOMP._IOwnership _out538;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out539;
            (this).GenExpr(_1912_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out537, out _out538, out _out539);
            _1915_exprGen = _out537;
            _1916___v149 = _out538;
            _1917_recIdents = _out539;
            RAST._IType _1918_dTypePath;
            RAST._IType _out540;
            _out540 = DCOMP.COMP.GenPath(_1913_dType);
            _1918_dTypePath = _out540;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_1915_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_1918_dTypePath).MSel(DCOMP.__default.escapeName(_1914_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out541;
            DCOMP._IOwnership _out542;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out541, out _out542);
            r = _out541;
            resultingOwnership = _out542;
            readIdents = _1917_recIdents;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_BoolBoundedPool) {
          unmatched74 = false;
          {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
            RAST._IExpr _out543;
            DCOMP._IOwnership _out544;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out543, out _out544);
            r = _out543;
            resultingOwnership = _out544;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SetBoundedPool) {
          DAST._IExpression _1919_of = _source74.dtor_of;
          unmatched74 = false;
          {
            RAST._IExpr _1920_exprGen;
            DCOMP._IOwnership _1921___v150;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1922_recIdents;
            RAST._IExpr _out545;
            DCOMP._IOwnership _out546;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out547;
            (this).GenExpr(_1919_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out545, out _out546, out _out547);
            _1920_exprGen = _out545;
            _1921___v150 = _out546;
            _1922_recIdents = _out547;
            r = ((((_1920_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out548;
            DCOMP._IOwnership _out549;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out548, out _out549);
            r = _out548;
            resultingOwnership = _out549;
            readIdents = _1922_recIdents;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SeqBoundedPool) {
          DAST._IExpression _1923_of = _source74.dtor_of;
          bool _1924_includeDuplicates = _source74.dtor_includeDuplicates;
          unmatched74 = false;
          {
            RAST._IExpr _1925_exprGen;
            DCOMP._IOwnership _1926___v151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1927_recIdents;
            RAST._IExpr _out550;
            DCOMP._IOwnership _out551;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out552;
            (this).GenExpr(_1923_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out550, out _out551, out _out552);
            _1925_exprGen = _out550;
            _1926___v151 = _out551;
            _1927_recIdents = _out552;
            r = ((_1925_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_1924_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out553;
            DCOMP._IOwnership _out554;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out553, out _out554);
            r = _out553;
            resultingOwnership = _out554;
            readIdents = _1927_recIdents;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_IntRange) {
          DAST._IExpression _1928_lo = _source74.dtor_lo;
          DAST._IExpression _1929_hi = _source74.dtor_hi;
          unmatched74 = false;
          {
            RAST._IExpr _1930_lo;
            DCOMP._IOwnership _1931___v152;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1932_recIdentsLo;
            RAST._IExpr _out555;
            DCOMP._IOwnership _out556;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out557;
            (this).GenExpr(_1928_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out555, out _out556, out _out557);
            _1930_lo = _out555;
            _1931___v152 = _out556;
            _1932_recIdentsLo = _out557;
            RAST._IExpr _1933_hi;
            DCOMP._IOwnership _1934___v153;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1935_recIdentsHi;
            RAST._IExpr _out558;
            DCOMP._IOwnership _out559;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out560;
            (this).GenExpr(_1929_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out558, out _out559, out _out560);
            _1933_hi = _out558;
            _1934___v153 = _out559;
            _1935_recIdentsHi = _out560;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1930_lo, _1933_hi));
            RAST._IExpr _out561;
            DCOMP._IOwnership _out562;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out561, out _out562);
            r = _out561;
            resultingOwnership = _out562;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1932_recIdentsLo, _1935_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MapBuilder) {
          DAST._IType _1936_keyType = _source74.dtor_keyType;
          DAST._IType _1937_valueType = _source74.dtor_valueType;
          unmatched74 = false;
          {
            RAST._IType _1938_kType;
            RAST._IType _out563;
            _out563 = (this).GenType(_1936_keyType, false, false);
            _1938_kType = _out563;
            RAST._IType _1939_vType;
            RAST._IType _out564;
            _out564 = (this).GenType(_1937_valueType, false, false);
            _1939_vType = _out564;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1938_kType, _1939_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out565;
            DCOMP._IOwnership _out566;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out565, out _out566);
            r = _out565;
            resultingOwnership = _out566;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched74) {
        DAST._IType _1940_elemType = _source74.dtor_elemType;
        unmatched74 = false;
        {
          RAST._IType _1941_eType;
          RAST._IType _out567;
          _out567 = (this).GenType(_1940_elemType, false, false);
          _1941_eType = _out567;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1941_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out568;
          DCOMP._IOwnership _out569;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out568, out _out569);
          r = _out568;
          resultingOwnership = _out569;
          return ;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      BigInteger _1942_i;
      _1942_i = BigInteger.Zero;
      while ((_1942_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _1943_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _1944_m;
        RAST._IMod _out570;
        _out570 = (this).GenModule((p).Select(_1942_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _1944_m = _out570;
        _1943_generated = (_1944_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_1942_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _1943_generated);
        _1942_i = (_1942_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _1945_i;
      _1945_i = BigInteger.Zero;
      while ((_1945_i) < (new BigInteger((fullName).Count))) {
        if ((_1945_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_1945_i)));
        _1945_i = (_1945_i) + (BigInteger.One);
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