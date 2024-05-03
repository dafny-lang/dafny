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
      Dafny.ISequence<Dafny.Rune> _2217___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_2217___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _2217___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_2217___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in115 = (i).Drop(new BigInteger(2));
        i = _in115;
        goto TAIL_CALL_START;
      } else {
        _2217___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_2217___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in116 = (i).Drop(BigInteger.One);
        i = _in116;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _2218___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_2218___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _2218___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_2218___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in117 = (i).Drop(BigInteger.One);
        i = _in117;
        goto TAIL_CALL_START;
      } else {
        _2218___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_2218___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _2219_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _2219_r);
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
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _i_names;
    public readonly Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _i_types;
    public Environment(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> names, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> types) {
      this._i_names = names;
      this._i_types = types;
    }
    public _IEnvironment DowncastClone() {
      if (this is _IEnvironment dt) { return dt; }
      return new Environment(_i_names, _i_types);
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.Environment;
      return oth != null && object.Equals(this._i_names, oth._i_names) && object.Equals(this._i_types, oth._i_types);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_names));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_types));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.Environment.Environment";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_names);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_types);
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
        return this._i_names;
      }
    }
    public Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> dtor_types {
      get {
        return this._i_types;
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
      BigInteger _2220_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _2220_indexInEnv), ((this).dtor_names).Drop((_2220_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
    }
  }

  public partial class COMP {
    public COMP() {
      this.error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.Default();
      this._i_UnicodeChars = false;
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> error {get; set;}
    public void __ctor(bool unicodeChars)
    {
      (this)._i_UnicodeChars = unicodeChars;
      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
    }
    public RAST._IMod GenModule(DAST._IModule mod, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      RAST._IMod s = RAST.Mod.Default();
      Dafny.ISequence<Dafny.Rune> _2221_modName;
      _2221_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_2221_modName);
      } else {
        Dafny.ISequence<RAST._IModDecl> _2222_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _2222_body = _out15;
        s = RAST.Mod.create_Mod(_2221_modName, _2222_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi5 = new BigInteger((body).Count);
      for (BigInteger _2223_i = BigInteger.Zero; _2223_i < _hi5; _2223_i++) {
        Dafny.ISequence<RAST._IModDecl> _2224_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source69 = (body).Select(_2223_i);
        if (_source69.is_Module) {
          DAST._IModule _2225___mcc_h0 = _source69.dtor_Module_i_a0;
          DAST._IModule _2226_m = _2225___mcc_h0;
          RAST._IMod _2227_mm;
          RAST._IMod _out16;
          _out16 = (this).GenModule(_2226_m, containingPath);
          _2227_mm = _out16;
          _2224_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_2227_mm));
        } else if (_source69.is_Class) {
          DAST._IClass _2228___mcc_h1 = _source69.dtor_Class_i_a0;
          DAST._IClass _2229_c = _2228___mcc_h1;
          Dafny.ISequence<RAST._IModDecl> _out17;
          _out17 = (this).GenClass(_2229_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_2229_c).dtor_name)));
          _2224_generated = _out17;
        } else if (_source69.is_Trait) {
          DAST._ITrait _2230___mcc_h2 = _source69.dtor_Trait_i_a0;
          DAST._ITrait _2231_t = _2230___mcc_h2;
          Dafny.ISequence<Dafny.Rune> _2232_tt;
          Dafny.ISequence<Dafny.Rune> _out18;
          _out18 = (this).GenTrait(_2231_t, containingPath);
          _2232_tt = _out18;
          _2224_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_RawDecl(_2232_tt));
        } else if (_source69.is_Newtype) {
          DAST._INewtype _2233___mcc_h3 = _source69.dtor_Newtype_i_a0;
          DAST._INewtype _2234_n = _2233___mcc_h3;
          Dafny.ISequence<RAST._IModDecl> _out19;
          _out19 = (this).GenNewtype(_2234_n);
          _2224_generated = _out19;
        } else if (_source69.is_SynonymType) {
          DAST._ISynonymType _2235___mcc_h4 = _source69.dtor_SynonymType_i_a0;
          DAST._ISynonymType _2236_s = _2235___mcc_h4;
          Dafny.ISequence<RAST._IModDecl> _out20;
          _out20 = (this).GenSynonymType(_2236_s);
          _2224_generated = _out20;
        } else {
          DAST._IDatatype _2237___mcc_h5 = _source69.dtor_Datatype_i_a0;
          DAST._IDatatype _2238_d = _2237___mcc_h5;
          Dafny.ISequence<RAST._IModDecl> _out21;
          _out21 = (this).GenDatatype(_2238_d);
          _2224_generated = _out21;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _2224_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _2239_genTpConstraint;
      _2239_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _2239_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_2239_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _2239_genTpConstraint);
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
        for (BigInteger _2240_tpI = BigInteger.Zero; _2240_tpI < _hi6; _2240_tpI++) {
          DAST._ITypeArgDecl _2241_tp;
          _2241_tp = (@params).Select(_2240_tpI);
          DAST._IType _2242_typeArg;
          RAST._ITypeParamDecl _2243_typeParam;
          DAST._IType _out22;
          RAST._ITypeParamDecl _out23;
          (this).GenTypeParam(_2241_tp, out _out22, out _out23);
          _2242_typeArg = _out22;
          _2243_typeParam = _out23;
          RAST._IType _2244_rType;
          RAST._IType _out24;
          _out24 = (this).GenType(_2242_typeArg, false, false);
          _2244_rType = _out24;
          typeParamsSet = Dafny.Set<DAST._IType>.Union(typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_2242_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_2244_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_2243_typeParam));
        }
      }
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _2245_typeParamsSet;
      Dafny.ISequence<RAST._IType> _2246_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2247_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _2248_whereConstraints;
      Dafny.ISet<DAST._IType> _out25;
      Dafny.ISequence<RAST._IType> _out26;
      Dafny.ISequence<RAST._ITypeParamDecl> _out27;
      Dafny.ISequence<Dafny.Rune> _out28;
      (this).GenTypeParameters((c).dtor_typeParams, out _out25, out _out26, out _out27, out _out28);
      _2245_typeParamsSet = _out25;
      _2246_rTypeParams = _out26;
      _2247_rTypeParamsDecls = _out27;
      _2248_whereConstraints = _out28;
      Dafny.ISequence<Dafny.Rune> _2249_constrainedTypeParams;
      _2249_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_2247_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _2250_fields;
      _2250_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _2251_fieldInits;
      _2251_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _2252_fieldI = BigInteger.Zero; _2252_fieldI < _hi7; _2252_fieldI++) {
        DAST._IField _2253_field;
        _2253_field = ((c).dtor_fields).Select(_2252_fieldI);
        RAST._IType _2254_fieldType;
        RAST._IType _out29;
        _out29 = (this).GenType(((_2253_field).dtor_formal).dtor_typ, false, false);
        _2254_fieldType = _out29;
        Dafny.ISequence<Dafny.Rune> _2255_fieldRustName;
        _2255_fieldRustName = DCOMP.__default.escapeName(((_2253_field).dtor_formal).dtor_name);
        _2250_fields = Dafny.Sequence<RAST._IField>.Concat(_2250_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_2255_fieldRustName, _2254_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source70 = (_2253_field).dtor_defaultValue;
        if (_source70.is_None) {
          {
            RAST._IExpr _2256_default;
            _2256_default = RAST.__default.std__Default__default;
            _2251_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2251_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_2255_fieldRustName, _2256_default)));
          }
        } else {
          DAST._IExpression _2257___mcc_h0 = _source70.dtor_value;
          DAST._IExpression _2258_e = _2257___mcc_h0;
          {
            RAST._IExpr _2259_expr;
            DCOMP._IOwnership _2260___v39;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2261___v40;
            RAST._IExpr _out30;
            DCOMP._IOwnership _out31;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
            (this).GenExpr(_2258_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
            _2259_expr = _out30;
            _2260___v39 = _out31;
            _2261___v40 = _out32;
            _2251_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2251_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_2253_field).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cell::RefCell::new("), (_2259_expr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))))));
          }
        }
      }
      BigInteger _hi8 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _2262_typeParamI = BigInteger.Zero; _2262_typeParamI < _hi8; _2262_typeParamI++) {
        DAST._IType _2263_typeArg;
        RAST._ITypeParamDecl _2264_typeParam;
        DAST._IType _out33;
        RAST._ITypeParamDecl _out34;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_2262_typeParamI), out _out33, out _out34);
        _2263_typeArg = _out33;
        _2264_typeParam = _out34;
        RAST._IType _2265_rTypeArg;
        RAST._IType _out35;
        _out35 = (this).GenType(_2263_typeArg, false, false);
        _2265_rTypeArg = _out35;
        _2250_fields = Dafny.Sequence<RAST._IField>.Concat(_2250_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_2262_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_2265_rTypeArg))))));
        _2251_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2251_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_2262_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      Dafny.ISequence<Dafny.Rune> _2266_datatypeName;
      _2266_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IStruct _2267_struct;
      _2267_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _2266_datatypeName, _2247_rTypeParamsDecls, RAST.Fields.create_NamedFields(_2250_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_2267_struct));
      Dafny.ISequence<RAST._IImplMember> _2268_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _2269_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out36;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out37;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(path, (c).dtor_attributes))), _2245_typeParamsSet, out _out36, out _out37);
      _2268_implBodyRaw = _out36;
      _2269_traitBodies = _out37;
      Dafny.ISequence<RAST._IImplMember> _2270_implBody;
      _2270_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(RAST.Expr.create_Identifier(_2266_datatypeName), _2251_fieldInits))))), _2268_implBodyRaw);
      RAST._IImpl _2271_i;
      _2271_i = RAST.Impl.create_Impl(_2247_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2266_datatypeName), _2246_rTypeParams), _2248_whereConstraints, _2270_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_2271_i)));
      if ((new BigInteger(((c).dtor_superClasses).Count)).Sign == 1) {
        BigInteger _2272_i;
        _2272_i = BigInteger.Zero;
        while ((_2272_i) < (new BigInteger(((c).dtor_superClasses).Count))) {
          DAST._IType _2273_superClass;
          _2273_superClass = ((c).dtor_superClasses).Select(_2272_i);
          DAST._IType _source71 = _2273_superClass;
          if (_source71.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2274___mcc_h1 = _source71.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _2275___mcc_h2 = _source71.dtor_typeArgs;
            DAST._IResolvedType _2276___mcc_h3 = _source71.dtor_resolved;
            DAST._IResolvedType _source72 = _2276___mcc_h3;
            if (_source72.is_Datatype) {
              DAST._IDatatypeType _2277___mcc_h7 = _source72.dtor_datatypeType;
            } else if (_source72.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2278___mcc_h9 = _source72.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _2279___mcc_h10 = _source72.dtor_attributes;
              Dafny.ISequence<DAST._IType> _2280_typeArgs = _2275___mcc_h2;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2281_traitPath = _2274___mcc_h1;
              {
                RAST._IType _2282_pathStr;
                RAST._IType _out38;
                _out38 = DCOMP.COMP.GenPath(_2281_traitPath);
                _2282_pathStr = _out38;
                Dafny.ISequence<RAST._IType> _2283_typeArgs;
                Dafny.ISequence<RAST._IType> _out39;
                _out39 = (this).GenTypeArgs(_2280_typeArgs, false, false);
                _2283_typeArgs = _out39;
                Dafny.ISequence<RAST._IImplMember> _2284_body;
                _2284_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_2269_traitBodies).Contains(_2281_traitPath)) {
                  _2284_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_2269_traitBodies,_2281_traitPath);
                }
                RAST._IType _2285_genSelfPath;
                RAST._IType _out40;
                _out40 = DCOMP.COMP.GenPath(path);
                _2285_genSelfPath = _out40;
                RAST._IModDecl _2286_x;
                _2286_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2247_rTypeParamsDecls, RAST.Type.create_TypeApp(_2282_pathStr, _2283_typeArgs), RAST.__default.Rc(RAST.Type.create_TypeApp(_2285_genSelfPath, _2246_rTypeParams)), _2248_whereConstraints, _2284_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_2286_x));
              }
            } else {
              DAST._IType _2287___mcc_h13 = _source72.dtor_baseType;
              DAST._INewtypeRange _2288___mcc_h14 = _source72.dtor_range;
              bool _2289___mcc_h15 = _source72.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _2290___mcc_h16 = _source72.dtor_attributes;
            }
          } else if (_source71.is_Nullable) {
            DAST._IType _2291___mcc_h21 = _source71.dtor_Nullable_i_a0;
          } else if (_source71.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2292___mcc_h23 = _source71.dtor_Tuple_i_a0;
          } else if (_source71.is_Array) {
            DAST._IType _2293___mcc_h25 = _source71.dtor_element;
            BigInteger _2294___mcc_h26 = _source71.dtor_dims;
          } else if (_source71.is_Seq) {
            DAST._IType _2295___mcc_h29 = _source71.dtor_element;
          } else if (_source71.is_Set) {
            DAST._IType _2296___mcc_h31 = _source71.dtor_element;
          } else if (_source71.is_Multiset) {
            DAST._IType _2297___mcc_h33 = _source71.dtor_element;
          } else if (_source71.is_Map) {
            DAST._IType _2298___mcc_h35 = _source71.dtor_key;
            DAST._IType _2299___mcc_h36 = _source71.dtor_value;
          } else if (_source71.is_SetBuilder) {
            DAST._IType _2300___mcc_h39 = _source71.dtor_element;
          } else if (_source71.is_MapBuilder) {
            DAST._IType _2301___mcc_h41 = _source71.dtor_key;
            DAST._IType _2302___mcc_h42 = _source71.dtor_value;
          } else if (_source71.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2303___mcc_h45 = _source71.dtor_args;
            DAST._IType _2304___mcc_h46 = _source71.dtor_result;
          } else if (_source71.is_Primitive) {
            DAST._IPrimitive _2305___mcc_h49 = _source71.dtor_Primitive_i_a0;
          } else if (_source71.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2306___mcc_h51 = _source71.dtor_Passthrough_i_a0;
          } else {
            Dafny.ISequence<Dafny.Rune> _2307___mcc_h53 = _source71.dtor_TypeArg_i_a0;
          }
          _2272_i = (_2272_i) + (BigInteger.One);
        }
      }
      RAST._IImpl _2308_d;
      _2308_d = RAST.Impl.create_ImplFor(_2247_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2266_datatypeName), _2246_rTypeParams), _2248_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(_2266_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new()"))))))));
      Dafny.ISequence<RAST._IModDecl> _2309_defaultImpl;
      _2309_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_2308_d));
      RAST._IImpl _2310_p;
      _2310_p = RAST.Impl.create_ImplFor(_2247_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2266_datatypeName), _2246_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), DCOMP.__default.escapeName(((c).dtor_enclosingModule))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")"))))))));
      Dafny.ISequence<RAST._IModDecl> _2311_printImpl;
      _2311_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_2310_p));
      RAST._IImpl _2312_pp;
      _2312_pp = RAST.Impl.create_ImplFor(_2247_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cmp::PartialEq")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2266_datatypeName), _2246_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("eq"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.__default.SelfBorrowed)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ptr::eq(self, other)")))))));
      Dafny.ISequence<RAST._IModDecl> _2313_ptrPartialEqImpl;
      _2313_ptrPartialEqImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_2312_pp));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(s, _2309_defaultImpl), _2311_printImpl), _2313_ptrPartialEqImpl);
      return s;
    }
    public Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _2314_typeParamsSet;
      _2314_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _2315_typeParamDecls;
      _2315_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _2316_typeParams;
      _2316_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _2317_tpI;
      _2317_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        while ((_2317_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._ITypeArgDecl _2318_tp;
          _2318_tp = ((t).dtor_typeParams).Select(_2317_tpI);
          DAST._IType _2319_typeArg;
          RAST._ITypeParamDecl _2320_typeParamDecl;
          DAST._IType _out41;
          RAST._ITypeParamDecl _out42;
          (this).GenTypeParam(_2318_tp, out _out41, out _out42);
          _2319_typeArg = _out41;
          _2320_typeParamDecl = _out42;
          _2314_typeParamsSet = Dafny.Set<DAST._IType>.Union(_2314_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_2319_typeArg));
          _2315_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_2315_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_2320_typeParamDecl));
          RAST._IType _2321_typeParam;
          RAST._IType _out43;
          _out43 = (this).GenType(_2319_typeArg, false, false);
          _2321_typeParam = _out43;
          _2316_typeParams = Dafny.Sequence<RAST._IType>.Concat(_2316_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_2321_typeParam));
          _2317_tpI = (_2317_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2322_fullPath;
      _2322_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _2323_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _2324___v44;
      Dafny.ISequence<RAST._IImplMember> _out44;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out45;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_2322_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_2322_fullPath, (t).dtor_attributes)), _2314_typeParamsSet, out _out44, out _out45);
      _2323_implBody = _out44;
      _2324___v44 = _out45;
      s = (RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_2315_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _2316_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _2323_implBody)))._ToString(DCOMP.__default.IND);
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _2325_typeParamsSet;
      Dafny.ISequence<RAST._IType> _2326_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2327_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _2328_whereConstraints;
      Dafny.ISet<DAST._IType> _out46;
      Dafny.ISequence<RAST._IType> _out47;
      Dafny.ISequence<RAST._ITypeParamDecl> _out48;
      Dafny.ISequence<Dafny.Rune> _out49;
      (this).GenTypeParameters((c).dtor_typeParams, out _out46, out _out47, out _out48, out _out49);
      _2325_typeParamsSet = _out46;
      _2326_rTypeParams = _out47;
      _2327_rTypeParamsDecls = _out48;
      _2328_whereConstraints = _out49;
      Dafny.ISequence<Dafny.Rune> _2329_constrainedTypeParams;
      _2329_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_2327_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _2330_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source73 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      if (_source73.is_None) {
        RAST._IType _out50;
        _out50 = (this).GenType((c).dtor_base, false, false);
        _2330_underlyingType = _out50;
      } else {
        RAST._IType _2331___mcc_h0 = _source73.dtor_value;
        RAST._IType _2332_v = _2331___mcc_h0;
        _2330_underlyingType = _2332_v;
      }
      DAST._IType _2333_resultingType;
      _2333_resultingType = DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Newtype((c).dtor_base, (c).dtor_range, false, (c).dtor_attributes));
      Dafny.ISequence<Dafny.Rune> _2334_datatypeName;
      _2334_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _2334_datatypeName, _2327_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _2330_underlyingType))))));
      RAST._IExpr _2335_fnBody;
      _2335_fnBody = RAST.Expr.create_Identifier(_2334_datatypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source74 = (c).dtor_witnessExpr;
      if (_source74.is_None) {
        {
          _2335_fnBody = (_2335_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      } else {
        DAST._IExpression _2336___mcc_h1 = _source74.dtor_value;
        DAST._IExpression _2337_e = _2336___mcc_h1;
        {
          DAST._IExpression _2338_e;
          _2338_e = ((object.Equals((c).dtor_base, _2333_resultingType)) ? (_2337_e) : (DAST.Expression.create_Convert(_2337_e, (c).dtor_base, _2333_resultingType)));
          RAST._IExpr _2339_eStr;
          DCOMP._IOwnership _2340___v45;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2341___v46;
          RAST._IExpr _out51;
          DCOMP._IOwnership _out52;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out53;
          (this).GenExpr(_2338_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out51, out _out52, out _out53);
          _2339_eStr = _out51;
          _2340___v45 = _out52;
          _2341___v46 = _out53;
          _2335_fnBody = (_2335_fnBody).Apply1(_2339_eStr);
        }
      }
      RAST._IImplMember _2342_body;
      _2342_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2335_fnBody)));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2327_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2334_datatypeName), _2326_rTypeParams), _2328_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_2342_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2327_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2334_datatypeName), _2326_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2327_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2334_datatypeName), _2326_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_2330_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _2343_typeParamsSet;
      Dafny.ISequence<RAST._IType> _2344_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2345_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _2346_whereConstraints;
      Dafny.ISet<DAST._IType> _out54;
      Dafny.ISequence<RAST._IType> _out55;
      Dafny.ISequence<RAST._ITypeParamDecl> _out56;
      Dafny.ISequence<Dafny.Rune> _out57;
      (this).GenTypeParameters((c).dtor_typeParams, out _out54, out _out55, out _out56, out _out57);
      _2343_typeParamsSet = _out54;
      _2344_rTypeParams = _out55;
      _2345_rTypeParamsDecls = _out56;
      _2346_whereConstraints = _out57;
      Dafny.ISequence<Dafny.Rune> _2347_constrainedTypeParams;
      _2347_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_2345_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<Dafny.Rune> _2348_synonymTypeName;
      _2348_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _2349_resultingType;
      RAST._IType _out58;
      _out58 = (this).GenType((c).dtor_base, false, false);
      _2349_resultingType = _out58;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _2348_synonymTypeName, _2345_rTypeParamsDecls, _2349_resultingType)));
      Std.Wrappers._IOption<DAST._IExpression> _source75 = (c).dtor_witnessExpr;
      if (_source75.is_None) {
      } else {
        DAST._IExpression _2350___mcc_h0 = _source75.dtor_value;
        DAST._IExpression _2351_e = _2350___mcc_h0;
        {
          RAST._IExpr _2352_rStmts;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2353___v47;
          DCOMP._IEnvironment _2354_newEnv;
          RAST._IExpr _out59;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out60;
          DCOMP._IEnvironment _out61;
          (this).GenStmts((c).dtor_witnessStmts, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), false, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out59, out _out60, out _out61);
          _2352_rStmts = _out59;
          _2353___v47 = _out60;
          _2354_newEnv = _out61;
          RAST._IExpr _2355_rExpr;
          DCOMP._IOwnership _2356___v48;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2357___v49;
          RAST._IExpr _out62;
          DCOMP._IOwnership _out63;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out64;
          (this).GenExpr(_2351_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), _2354_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out62, out _out63, out _out64);
          _2355_rExpr = _out62;
          _2356___v48 = _out63;
          _2357___v49 = _out64;
          Dafny.ISequence<Dafny.Rune> _2358_constantName;
          _2358_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_2358_constantName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_2349_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_2352_rStmts).Then(_2355_rExpr)))))));
        }
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _2359_typeParamsSet;
      Dafny.ISequence<RAST._IType> _2360_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2361_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _2362_whereConstraints;
      Dafny.ISet<DAST._IType> _out65;
      Dafny.ISequence<RAST._IType> _out66;
      Dafny.ISequence<RAST._ITypeParamDecl> _out67;
      Dafny.ISequence<Dafny.Rune> _out68;
      (this).GenTypeParameters((c).dtor_typeParams, out _out65, out _out66, out _out67, out _out68);
      _2359_typeParamsSet = _out65;
      _2360_rTypeParams = _out66;
      _2361_rTypeParamsDecls = _out67;
      _2362_whereConstraints = _out68;
      Dafny.ISequence<Dafny.Rune> _2363_datatypeName;
      _2363_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _2364_ctors;
      _2364_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      BigInteger _hi9 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _2365_i = BigInteger.Zero; _2365_i < _hi9; _2365_i++) {
        DAST._IDatatypeCtor _2366_ctor;
        _2366_ctor = ((c).dtor_ctors).Select(_2365_i);
        Dafny.ISequence<RAST._IField> _2367_ctorArgs;
        _2367_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        BigInteger _hi10 = new BigInteger(((_2366_ctor).dtor_args).Count);
        for (BigInteger _2368_j = BigInteger.Zero; _2368_j < _hi10; _2368_j++) {
          DAST._IFormal _2369_formal;
          _2369_formal = ((_2366_ctor).dtor_args).Select(_2368_j);
          RAST._IType _2370_formalType;
          RAST._IType _out69;
          _out69 = (this).GenType((_2369_formal).dtor_typ, false, false);
          _2370_formalType = _out69;
          if ((c).dtor_isCo) {
            _2367_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_2367_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(DCOMP.__default.escapeName((_2369_formal).dtor_name), RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_2370_formalType))))));
          } else {
            _2367_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_2367_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(DCOMP.__default.escapeName((_2369_formal).dtor_name), _2370_formalType))));
          }
        }
        _2364_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_2364_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_2366_ctor).dtor_name), RAST.Fields.create_NamedFields(_2367_ctorArgs))));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2371_selfPath;
      _2371_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _2372_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _2373_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out70;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out71;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(_2371_selfPath, (c).dtor_attributes))), _2359_typeParamsSet, out _out70, out _out71);
      _2372_implBodyRaw = _out70;
      _2373_traitBodies = _out71;
      Dafny.ISequence<RAST._IImplMember> _2374_implBody;
      _2374_implBody = _2372_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2375_emittedFields;
      _2375_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi11 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _2376_i = BigInteger.Zero; _2376_i < _hi11; _2376_i++) {
        DAST._IDatatypeCtor _2377_ctor;
        _2377_ctor = ((c).dtor_ctors).Select(_2376_i);
        BigInteger _hi12 = new BigInteger(((_2377_ctor).dtor_args).Count);
        for (BigInteger _2378_j = BigInteger.Zero; _2378_j < _hi12; _2378_j++) {
          DAST._IFormal _2379_formal;
          _2379_formal = ((_2377_ctor).dtor_args).Select(_2378_j);
          if (!((_2375_emittedFields).Contains((_2379_formal).dtor_name))) {
            _2375_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2375_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_2379_formal).dtor_name));
            RAST._IType _2380_formalType;
            RAST._IType _out72;
            _out72 = (this).GenType((_2379_formal).dtor_typ, false, false);
            _2380_formalType = _out72;
            Dafny.ISequence<RAST._IMatchCase> _2381_cases;
            _2381_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _2382_k = BigInteger.Zero; _2382_k < _hi13; _2382_k++) {
              DAST._IDatatypeCtor _2383_ctor2;
              _2383_ctor2 = ((c).dtor_ctors).Select(_2382_k);
              Dafny.ISequence<Dafny.Rune> _2384_pattern;
              _2384_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2363_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_2383_ctor2).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
              Dafny.ISequence<Dafny.Rune> _2385_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              bool _2386_hasMatchingField;
              _2386_hasMatchingField = false;
              BigInteger _hi14 = new BigInteger(((_2383_ctor2).dtor_args).Count);
              for (BigInteger _2387_l = BigInteger.Zero; _2387_l < _hi14; _2387_l++) {
                DAST._IFormal _2388_formal2;
                _2388_formal2 = ((_2383_ctor2).dtor_args).Select(_2387_l);
                if (object.Equals((_2379_formal).dtor_name, (_2388_formal2).dtor_name)) {
                  _2386_hasMatchingField = true;
                }
                _2384_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2384_pattern, DCOMP.__default.escapeName((_2388_formal2).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2384_pattern = Dafny.Sequence<Dafny.Rune>.Concat(_2384_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              if (_2386_hasMatchingField) {
                if ((c).dtor_isCo) {
                  _2385_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), DCOMP.__default.escapeName((_2379_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _2385_rhs = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeName((_2379_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _2385_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _2389_ctorMatch;
              _2389_ctorMatch = RAST.MatchCase.create(_2384_pattern, RAST.Expr.create_RawExpr(_2385_rhs));
              _2381_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_2381_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_2389_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _2381_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_2381_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_2363_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _2390_methodBody;
            _2390_methodBody = RAST.Expr.create_Match(RAST.__default.self, _2381_cases);
            _2374_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_2374_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(DCOMP.__default.escapeName((_2379_formal).dtor_name), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_2380_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2390_methodBody)))));
          }
        }
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _2391_types;
        _2391_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi15 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _2392_typeI = BigInteger.Zero; _2392_typeI < _hi15; _2392_typeI++) {
          DAST._IType _2393_typeArg;
          RAST._ITypeParamDecl _2394_rTypeParamDecl;
          DAST._IType _out73;
          RAST._ITypeParamDecl _out74;
          (this).GenTypeParam(((c).dtor_typeParams).Select(_2392_typeI), out _out73, out _out74);
          _2393_typeArg = _out73;
          _2394_rTypeParamDecl = _out74;
          RAST._IType _2395_rTypeArg;
          RAST._IType _out75;
          _out75 = (this).GenType(_2393_typeArg, false, false);
          _2395_rTypeArg = _out75;
          _2391_types = Dafny.Sequence<RAST._IType>.Concat(_2391_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_2395_rTypeArg))));
        }
        _2364_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_2364_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_2396_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _2396_tpe);
})), _2391_types)))));
      }
      Dafny.ISequence<RAST._IModDecl> _2397_enumBody;
      _2397_enumBody = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]")), _2363_datatypeName, _2361_rTypeParamsDecls, _2364_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_2361_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2363_datatypeName), _2360_rTypeParams), _2362_whereConstraints, _2374_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _2398_printImplBodyCases;
      _2398_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _2399_i = BigInteger.Zero; _2399_i < _hi16; _2399_i++) {
        DAST._IDatatypeCtor _2400_ctor;
        _2400_ctor = ((c).dtor_ctors).Select(_2399_i);
        Dafny.ISequence<Dafny.Rune> _2401_ctorMatch;
        _2401_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeName((_2400_ctor).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
        Dafny.ISequence<Dafny.Rune> _2402_modulePrefix;
        _2402_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeName(((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        RAST._IExpr _2403_printRhs;
        _2403_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _2402_modulePrefix), DCOMP.__default.escapeName((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName((_2400_ctor).dtor_name)), (((_2400_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        BigInteger _hi17 = new BigInteger(((_2400_ctor).dtor_args).Count);
        for (BigInteger _2404_j = BigInteger.Zero; _2404_j < _hi17; _2404_j++) {
          DAST._IFormal _2405_formal;
          _2405_formal = ((_2400_ctor).dtor_args).Select(_2404_j);
          Dafny.ISequence<Dafny.Rune> _2406_formalName;
          _2406_formalName = DCOMP.__default.escapeName((_2405_formal).dtor_name);
          _2401_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2401_ctorMatch, _2406_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_2404_j).Sign == 1) {
            _2403_printRhs = (_2403_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _2403_printRhs = (_2403_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), DCOMP.__default.escapeName((_2405_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))));
        }
        _2401_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(_2401_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        if ((_2400_ctor).dtor_hasAnyArgs) {
          _2403_printRhs = (_2403_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _2403_printRhs = (_2403_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _2398_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_2398_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2363_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _2401_ctorMatch), RAST.Expr.create_Block(_2403_printRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _2398_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_2398_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_2363_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _2407_defaultConstrainedTypeParams;
      _2407_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_2361_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      RAST._IExpr _2408_printImplBody;
      _2408_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _2398_printImplBodyCases);
      Dafny.ISequence<RAST._IModDecl> _2409_printImpl;
      _2409_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2361_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2363_datatypeName), _2360_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2361_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2363_datatypeName), _2360_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2408_printImplBody)))))));
      Dafny.ISequence<RAST._IModDecl> _2410_defaultImpl;
      _2410_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _2411_structName;
        _2411_structName = (RAST.Expr.create_Identifier(_2363_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _2412_structAssignments;
        _2412_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi18 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _2413_i = BigInteger.Zero; _2413_i < _hi18; _2413_i++) {
          DAST._IFormal _2414_formal;
          _2414_formal = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_2413_i);
          _2412_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2412_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName((_2414_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _2415_defaultConstrainedTypeParams;
        _2415_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_2361_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _2416_fullType;
        _2416_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2363_datatypeName), _2360_rTypeParams);
        _2410_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2415_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _2416_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_2416_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_2411_structName, _2412_structAssignments))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(_2397_enumBody, _2409_printImpl), _2410_defaultImpl);
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
        for (BigInteger _2417_i = BigInteger.Zero; _2417_i < _hi19; _2417_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_2417_i))));
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
        for (BigInteger _2418_i = BigInteger.Zero; _2418_i < _hi20; _2418_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_2418_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding, bool inFn)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger((args).Count)).Sign == 1) {
        BigInteger _2419_i;
        _2419_i = BigInteger.Zero;
        while ((_2419_i) < (new BigInteger((args).Count))) {
          RAST._IType _2420_genTp;
          RAST._IType _out76;
          _out76 = (this).GenType((args).Select(_2419_i), inBinding, inFn);
          _2420_genTp = _out76;
          s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_2420_genTp));
          _2419_i = (_2419_i) + (BigInteger.One);
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
      DAST._IType _source76 = c;
      if (_source76.is_Path) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2421___mcc_h0 = _source76.dtor_Path_i_a0;
        Dafny.ISequence<DAST._IType> _2422___mcc_h1 = _source76.dtor_typeArgs;
        DAST._IResolvedType _2423___mcc_h2 = _source76.dtor_resolved;
        DAST._IResolvedType _2424_resolved = _2423___mcc_h2;
        Dafny.ISequence<DAST._IType> _2425_args = _2422___mcc_h1;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2426_p = _2421___mcc_h0;
        {
          RAST._IType _2427_t;
          RAST._IType _out77;
          _out77 = DCOMP.COMP.GenPath(_2426_p);
          _2427_t = _out77;
          Dafny.ISequence<RAST._IType> _2428_typeArgs;
          Dafny.ISequence<RAST._IType> _out78;
          _out78 = (this).GenTypeArgs(_2425_args, inBinding, inFn);
          _2428_typeArgs = _out78;
          s = RAST.Type.create_TypeApp(_2427_t, _2428_typeArgs);
          DAST._IResolvedType _source77 = _2424_resolved;
          if (_source77.is_Datatype) {
            DAST._IDatatypeType _2429___mcc_h21 = _source77.dtor_datatypeType;
            DAST._IDatatypeType _source78 = _2429___mcc_h21;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2430___mcc_h22 = _source78.dtor_path;
            Dafny.ISequence<DAST._IAttribute> _2431___mcc_h23 = _source78.dtor_attributes;
            Dafny.ISequence<DAST._IAttribute> _2432_attributes = _2431___mcc_h23;
          } else if (_source77.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2433___mcc_h24 = _source77.dtor_path;
            Dafny.ISequence<DAST._IAttribute> _2434___mcc_h25 = _source77.dtor_attributes;
            {
              if ((_2426_p).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc<dyn ::std::any::Any>"));
              } else {
                if (inBinding) {
                  s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
                } else {
                  s = RAST.Type.create_ImplType(s);
                }
              }
            }
          } else {
            DAST._IType _2435___mcc_h26 = _source77.dtor_baseType;
            DAST._INewtypeRange _2436___mcc_h27 = _source77.dtor_range;
            bool _2437___mcc_h28 = _source77.dtor_erase;
            Dafny.ISequence<DAST._IAttribute> _2438___mcc_h29 = _source77.dtor_attributes;
            Dafny.ISequence<DAST._IAttribute> _2439_attributes = _2438___mcc_h29;
            bool _2440_erased = _2437___mcc_h28;
            DAST._INewtypeRange _2441_range = _2436___mcc_h27;
            DAST._IType _2442_t = _2435___mcc_h26;
            {
              if (_2440_erased) {
                Std.Wrappers._IOption<RAST._IType> _source79 = DCOMP.COMP.NewtypeToRustType(_2442_t, _2441_range);
                if (_source79.is_None) {
                } else {
                  RAST._IType _2443___mcc_h30 = _source79.dtor_value;
                  RAST._IType _2444_v = _2443___mcc_h30;
                  s = _2444_v;
                }
              }
            }
          }
        }
      } else if (_source76.is_Nullable) {
        DAST._IType _2445___mcc_h3 = _source76.dtor_Nullable_i_a0;
        DAST._IType _2446_inner = _2445___mcc_h3;
        {
          RAST._IType _2447_innerExpr;
          RAST._IType _out79;
          _out79 = (this).GenType(_2446_inner, inBinding, inFn);
          _2447_innerExpr = _out79;
          s = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::option::Option")), Dafny.Sequence<RAST._IType>.FromElements(_2447_innerExpr));
        }
      } else if (_source76.is_Tuple) {
        Dafny.ISequence<DAST._IType> _2448___mcc_h4 = _source76.dtor_Tuple_i_a0;
        Dafny.ISequence<DAST._IType> _2449_types = _2448___mcc_h4;
        {
          Dafny.ISequence<RAST._IType> _2450_args;
          _2450_args = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _2451_i;
          _2451_i = BigInteger.Zero;
          while ((_2451_i) < (new BigInteger((_2449_types).Count))) {
            RAST._IType _2452_generated;
            RAST._IType _out80;
            _out80 = (this).GenType((_2449_types).Select(_2451_i), inBinding, inFn);
            _2452_generated = _out80;
            _2450_args = Dafny.Sequence<RAST._IType>.Concat(_2450_args, Dafny.Sequence<RAST._IType>.FromElements(_2452_generated));
            _2451_i = (_2451_i) + (BigInteger.One);
          }
          s = RAST.Type.create_TupleType(_2450_args);
        }
      } else if (_source76.is_Array) {
        DAST._IType _2453___mcc_h5 = _source76.dtor_element;
        BigInteger _2454___mcc_h6 = _source76.dtor_dims;
        BigInteger _2455_dims = _2454___mcc_h6;
        DAST._IType _2456_element = _2453___mcc_h5;
        {
          RAST._IType _2457_elem;
          RAST._IType _out81;
          _out81 = (this).GenType(_2456_element, inBinding, inFn);
          _2457_elem = _out81;
          s = _2457_elem;
          BigInteger _2458_i;
          _2458_i = BigInteger.Zero;
          while ((_2458_i) < (_2455_dims)) {
            s = RAST.__default.Rc(RAST.__default.RefCell(RAST.__default.Vec(s)));
            _2458_i = (_2458_i) + (BigInteger.One);
          }
        }
      } else if (_source76.is_Seq) {
        DAST._IType _2459___mcc_h7 = _source76.dtor_element;
        DAST._IType _2460_element = _2459___mcc_h7;
        {
          RAST._IType _2461_elem;
          RAST._IType _out82;
          _out82 = (this).GenType(_2460_element, inBinding, inFn);
          _2461_elem = _out82;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_2461_elem));
        }
      } else if (_source76.is_Set) {
        DAST._IType _2462___mcc_h8 = _source76.dtor_element;
        DAST._IType _2463_element = _2462___mcc_h8;
        {
          RAST._IType _2464_elem;
          RAST._IType _out83;
          _out83 = (this).GenType(_2463_element, inBinding, inFn);
          _2464_elem = _out83;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_2464_elem));
        }
      } else if (_source76.is_Multiset) {
        DAST._IType _2465___mcc_h9 = _source76.dtor_element;
        DAST._IType _2466_element = _2465___mcc_h9;
        {
          RAST._IType _2467_elem;
          RAST._IType _out84;
          _out84 = (this).GenType(_2466_element, inBinding, inFn);
          _2467_elem = _out84;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_2467_elem));
        }
      } else if (_source76.is_Map) {
        DAST._IType _2468___mcc_h10 = _source76.dtor_key;
        DAST._IType _2469___mcc_h11 = _source76.dtor_value;
        DAST._IType _2470_value = _2469___mcc_h11;
        DAST._IType _2471_key = _2468___mcc_h10;
        {
          RAST._IType _2472_keyType;
          RAST._IType _out85;
          _out85 = (this).GenType(_2471_key, inBinding, inFn);
          _2472_keyType = _out85;
          RAST._IType _2473_valueType;
          RAST._IType _out86;
          _out86 = (this).GenType(_2470_value, inBinding, inFn);
          _2473_valueType = _out86;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_2472_keyType, _2473_valueType));
        }
      } else if (_source76.is_SetBuilder) {
        DAST._IType _2474___mcc_h12 = _source76.dtor_element;
        DAST._IType _2475_elem = _2474___mcc_h12;
        {
          RAST._IType _2476_elemType;
          RAST._IType _out87;
          _out87 = (this).GenType(_2475_elem, inBinding, inFn);
          _2476_elemType = _out87;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_2476_elemType));
        }
      } else if (_source76.is_MapBuilder) {
        DAST._IType _2477___mcc_h13 = _source76.dtor_key;
        DAST._IType _2478___mcc_h14 = _source76.dtor_value;
        DAST._IType _2479_value = _2478___mcc_h14;
        DAST._IType _2480_key = _2477___mcc_h13;
        {
          RAST._IType _2481_keyType;
          RAST._IType _out88;
          _out88 = (this).GenType(_2480_key, inBinding, inFn);
          _2481_keyType = _out88;
          RAST._IType _2482_valueType;
          RAST._IType _out89;
          _out89 = (this).GenType(_2479_value, inBinding, inFn);
          _2482_valueType = _out89;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_2481_keyType, _2482_valueType));
        }
      } else if (_source76.is_Arrow) {
        Dafny.ISequence<DAST._IType> _2483___mcc_h15 = _source76.dtor_args;
        DAST._IType _2484___mcc_h16 = _source76.dtor_result;
        DAST._IType _2485_result = _2484___mcc_h16;
        Dafny.ISequence<DAST._IType> _2486_args = _2483___mcc_h15;
        {
          Dafny.ISequence<RAST._IType> _2487_argTypes;
          _2487_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _2488_i;
          _2488_i = BigInteger.Zero;
          while ((_2488_i) < (new BigInteger((_2486_args).Count))) {
            RAST._IType _2489_generated;
            RAST._IType _out90;
            _out90 = (this).GenType((_2486_args).Select(_2488_i), inBinding, true);
            _2489_generated = _out90;
            _2487_argTypes = Dafny.Sequence<RAST._IType>.Concat(_2487_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_2489_generated)));
            _2488_i = (_2488_i) + (BigInteger.One);
          }
          RAST._IType _2490_resultType;
          RAST._IType _out91;
          _out91 = (this).GenType(_2485_result, inBinding, (inFn) || (inBinding));
          _2490_resultType = _out91;
          s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_2487_argTypes, _2490_resultType)));
        }
      } else if (_source76.is_Primitive) {
        DAST._IPrimitive _2491___mcc_h17 = _source76.dtor_Primitive_i_a0;
        DAST._IPrimitive _2492_p = _2491___mcc_h17;
        {
          DAST._IPrimitive _source80 = _2492_p;
          if (_source80.is_Int) {
            s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
          } else if (_source80.is_Real) {
            s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
          } else if (_source80.is_String) {
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
          } else if (_source80.is_Bool) {
            s = RAST.Type.create_Bool();
          } else {
            s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
          }
        }
      } else if (_source76.is_Passthrough) {
        Dafny.ISequence<Dafny.Rune> _2493___mcc_h18 = _source76.dtor_Passthrough_i_a0;
        Dafny.ISequence<Dafny.Rune> _2494_v = _2493___mcc_h18;
        s = RAST.__default.RawType(_2494_v);
      } else {
        Dafny.ISequence<Dafny.Rune> _2495___mcc_h19 = _source76.dtor_TypeArg_i_a0;
        Dafny.ISequence<Dafny.Rune> _source81 = _2495___mcc_h19;
        Dafny.ISequence<Dafny.Rune> _2496___mcc_h20 = _source81;
        Dafny.ISequence<Dafny.Rune> _2497_name = _2496___mcc_h20;
        s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_2497_name));
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
      for (BigInteger _2498_i = BigInteger.Zero; _2498_i < _hi21; _2498_i++) {
        DAST._IMethod _source82 = (body).Select(_2498_i);
        DAST._IMethod _2499___mcc_h0 = _source82;
        DAST._IMethod _2500_m = _2499___mcc_h0;
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source83 = (_2500_m).dtor_overridingPath;
          if (_source83.is_None) {
            {
              RAST._IImplMember _2501_generated;
              RAST._IImplMember _out92;
              _out92 = (this).GenMethod(_2500_m, forTrait, enclosingType, enclosingTypeParams);
              _2501_generated = _out92;
              s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_2501_generated));
            }
          } else {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2502___mcc_h1 = _source83.dtor_value;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2503_p = _2502___mcc_h1;
            {
              Dafny.ISequence<RAST._IImplMember> _2504_existing;
              _2504_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
              if ((traitBodies).Contains(_2503_p)) {
                _2504_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_2503_p);
              }
              RAST._IImplMember _2505_genMethod;
              RAST._IImplMember _out93;
              _out93 = (this).GenMethod(_2500_m, true, enclosingType, enclosingTypeParams);
              _2505_genMethod = _out93;
              _2504_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_2504_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_2505_genMethod));
              traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_2503_p, _2504_existing)));
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
      for (BigInteger _2506_i = BigInteger.Zero; _2506_i < _hi22; _2506_i++) {
        DAST._IFormal _2507_param;
        _2507_param = (@params).Select(_2506_i);
        RAST._IType _2508_paramType;
        RAST._IType _out94;
        _out94 = (this).GenType((_2507_param).dtor_typ, false, false);
        _2508_paramType = _out94;
        if ((!((_2508_paramType).CanReadWithoutClone())) && (!((_2507_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _2508_paramType = RAST.Type.create_Borrowed(_2508_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_2507_param).dtor_name), _2508_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _2509_params;
      Dafny.ISequence<RAST._IFormal> _out95;
      _out95 = (this).GenParams((m).dtor_params);
      _2509_params = _out95;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2510_paramNames;
      _2510_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2511_paramTypes;
      _2511_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi23 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _2512_paramI = BigInteger.Zero; _2512_paramI < _hi23; _2512_paramI++) {
        DAST._IFormal _2513_dafny__formal;
        _2513_dafny__formal = ((m).dtor_params).Select(_2512_paramI);
        RAST._IFormal _2514_formal;
        _2514_formal = (_2509_params).Select(_2512_paramI);
        Dafny.ISequence<Dafny.Rune> _2515_name;
        _2515_name = (_2514_formal).dtor_name;
        _2510_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2510_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2515_name));
        _2511_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2511_paramTypes, _2515_name, (_2514_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _2516_fnName;
      _2516_fnName = DCOMP.__default.escapeName((m).dtor_name);
      Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2517_selfIdentifier;
      _2517_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _2518_selfId;
        _2518_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((_2516_fnName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_ctor"))) {
          _2518_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        if (forTrait) {
          RAST._IFormal _2519_selfFormal;
          _2519_selfFormal = RAST.Formal.selfBorrowedMut;
          _2509_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_2519_selfFormal), _2509_params);
        } else {
          RAST._IType _2520_tpe;
          RAST._IType _out96;
          _out96 = (this).GenType(enclosingType, false, false);
          _2520_tpe = _out96;
          if (!((_2520_tpe).CanReadWithoutClone())) {
            _2520_tpe = RAST.Type.create_Borrowed(_2520_tpe);
          }
          _2509_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_2518_selfId, _2520_tpe)), _2509_params);
        }
        _2517_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2518_selfId);
      }
      Dafny.ISequence<RAST._IType> _2521_retTypeArgs;
      _2521_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _2522_typeI;
      _2522_typeI = BigInteger.Zero;
      while ((_2522_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _2523_typeExpr;
        RAST._IType _out97;
        _out97 = (this).GenType(((m).dtor_outTypes).Select(_2522_typeI), false, false);
        _2523_typeExpr = _out97;
        _2521_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_2521_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_2523_typeExpr));
        _2522_typeI = (_2522_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _2524_visibility;
      _2524_visibility = RAST.Visibility.create_PUB();
      Dafny.ISequence<DAST._ITypeArgDecl> _2525_typeParamsFiltered;
      _2525_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi24 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _2526_typeParamI = BigInteger.Zero; _2526_typeParamI < _hi24; _2526_typeParamI++) {
        DAST._ITypeArgDecl _2527_typeParam;
        _2527_typeParam = ((m).dtor_typeParams).Select(_2526_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_2527_typeParam).dtor_name)))) {
          _2525_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_2525_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_2527_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _2528_typeParams;
      _2528_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_2525_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi25 = new BigInteger((_2525_typeParamsFiltered).Count);
        for (BigInteger _2529_i = BigInteger.Zero; _2529_i < _hi25; _2529_i++) {
          DAST._IType _2530_typeArg;
          RAST._ITypeParamDecl _2531_rTypeParamDecl;
          DAST._IType _out98;
          RAST._ITypeParamDecl _out99;
          (this).GenTypeParam((_2525_typeParamsFiltered).Select(_2529_i), out _out98, out _out99);
          _2530_typeArg = _out98;
          _2531_rTypeParamDecl = _out99;
          _2528_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_2528_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_2531_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _2532_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _2533_env = DCOMP.Environment.Default();
      RAST._IExpr _2534_preBody;
      _2534_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      if ((m).dtor_hasBody) {
        RAST._IExpr _2535_earlyReturn;
        _2535_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source84 = (m).dtor_outVars;
        if (_source84.is_None) {
        } else {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2536___mcc_h0 = _source84.dtor_value;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2537_outVars = _2536___mcc_h0;
          {
            Dafny.ISequence<RAST._IExpr> _2538_tupleArgs;
            _2538_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi26 = new BigInteger((_2537_outVars).Count);
            for (BigInteger _2539_outI = BigInteger.Zero; _2539_outI < _hi26; _2539_outI++) {
              Dafny.ISequence<Dafny.Rune> _2540_outVar;
              _2540_outVar = (_2537_outVars).Select(_2539_outI);
              RAST._IType _2541_outType;
              RAST._IType _out100;
              _out100 = (this).GenType(((m).dtor_outTypes).Select(_2539_outI), false, false);
              _2541_outType = _out100;
              Dafny.ISequence<Dafny.Rune> _2542_outName;
              _2542_outName = DCOMP.__default.escapeName((_2540_outVar));
              _2510_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2510_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2542_outName));
              RAST._IType _2543_outMaybeType;
              _2543_outMaybeType = (((_2541_outType).CanReadWithoutClone()) ? (_2541_outType) : (RAST.Type.create_Borrowed(_2541_outType)));
              _2511_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2511_paramTypes, _2542_outName, _2543_outMaybeType);
              RAST._IExpr _2544_outVarReturn;
              DCOMP._IOwnership _2545___v53;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2546___v54;
              RAST._IExpr _out101;
              DCOMP._IOwnership _out102;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out103;
              (this).GenExpr(DAST.Expression.create_Ident((_2540_outVar)), Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2542_outName), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>, RAST._IType>(_2542_outName, _2543_outMaybeType))), DCOMP.Ownership.create_OwnershipOwned(), out _out101, out _out102, out _out103);
              _2544_outVarReturn = _out101;
              _2545___v53 = _out102;
              _2546___v54 = _out103;
              _2538_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2538_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2544_outVarReturn));
            }
            if ((new BigInteger((_2538_tupleArgs).Count)) == (BigInteger.One)) {
              _2535_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_2538_tupleArgs).Select(BigInteger.Zero)));
            } else {
              _2535_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_2538_tupleArgs)));
            }
          }
        }
        _2533_env = DCOMP.Environment.create(_2510_paramNames, _2511_paramTypes);
        RAST._IExpr _2547_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2548___v55;
        DCOMP._IEnvironment _2549___v56;
        RAST._IExpr _out104;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out105;
        DCOMP._IEnvironment _out106;
        (this).GenStmts((m).dtor_body, _2517_selfIdentifier, _2533_env, true, _2535_earlyReturn, out _out104, out _out105, out _out106);
        _2547_body = _out104;
        _2548___v55 = _out105;
        _2549___v56 = _out106;
        _2532_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_2534_preBody).Then(_2547_body));
      } else {
        _2533_env = DCOMP.Environment.create(_2510_paramNames, _2511_paramTypes);
        _2532_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_2524_visibility, RAST.Fn.create(_2516_fnName, _2528_typeParams, _2509_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_2521_retTypeArgs).Count)) == (BigInteger.One)) ? ((_2521_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_2521_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _2532_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2550_declarations;
      _2550_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _2551_i;
      _2551_i = BigInteger.Zero;
      newEnv = env;
      while ((_2551_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _2552_stmt;
        _2552_stmt = (stmts).Select(_2551_i);
        RAST._IExpr _2553_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2554_recIdents;
        DCOMP._IEnvironment _2555_newEnv2;
        RAST._IExpr _out107;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out108;
        DCOMP._IEnvironment _out109;
        (this).GenStmt(_2552_stmt, selfIdent, newEnv, (isLast) && ((_2551_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out107, out _out108, out _out109);
        _2553_stmtExpr = _out107;
        _2554_recIdents = _out108;
        _2555_newEnv2 = _out109;
        newEnv = _2555_newEnv2;
        DAST._IStatement _source85 = _2552_stmt;
        if (_source85.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _2556___mcc_h0 = _source85.dtor_name;
          DAST._IType _2557___mcc_h1 = _source85.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> _2558___mcc_h2 = _source85.dtor_maybeValue;
          Dafny.ISequence<Dafny.Rune> _2559_name = _2556___mcc_h0;
          {
            _2550_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2550_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_2559_name)));
          }
        } else if (_source85.is_Assign) {
          DAST._IAssignLhs _2560___mcc_h6 = _source85.dtor_lhs;
          DAST._IExpression _2561___mcc_h7 = _source85.dtor_value;
        } else if (_source85.is_If) {
          DAST._IExpression _2562___mcc_h10 = _source85.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _2563___mcc_h11 = _source85.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _2564___mcc_h12 = _source85.dtor_els;
        } else if (_source85.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _2565___mcc_h16 = _source85.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _2566___mcc_h17 = _source85.dtor_body;
        } else if (_source85.is_While) {
          DAST._IExpression _2567___mcc_h20 = _source85.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _2568___mcc_h21 = _source85.dtor_body;
        } else if (_source85.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _2569___mcc_h24 = _source85.dtor_boundName;
          DAST._IType _2570___mcc_h25 = _source85.dtor_boundType;
          DAST._IExpression _2571___mcc_h26 = _source85.dtor_over;
          Dafny.ISequence<DAST._IStatement> _2572___mcc_h27 = _source85.dtor_body;
        } else if (_source85.is_Call) {
          DAST._IExpression _2573___mcc_h32 = _source85.dtor_on;
          DAST._ICallName _2574___mcc_h33 = _source85.dtor_callName;
          Dafny.ISequence<DAST._IType> _2575___mcc_h34 = _source85.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2576___mcc_h35 = _source85.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _2577___mcc_h36 = _source85.dtor_outs;
        } else if (_source85.is_Return) {
          DAST._IExpression _2578___mcc_h42 = _source85.dtor_expr;
        } else if (_source85.is_EarlyReturn) {
        } else if (_source85.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2579___mcc_h44 = _source85.dtor_toLabel;
        } else if (_source85.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _2580___mcc_h46 = _source85.dtor_body;
        } else if (_source85.is_JumpTailCallStart) {
        } else if (_source85.is_Halt) {
        } else {
          DAST._IExpression _2581___mcc_h48 = _source85.dtor_Print_i_a0;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2554_recIdents, _2550_declarations));
        generated = (generated).Then(_2553_stmtExpr);
        _2551_i = (_2551_i) + (BigInteger.One);
      }
    }
    public void GenAssignLhs(DAST._IAssignLhs lhs, RAST._IExpr rhs, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, out RAST._IExpr generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      newEnv = env;
      DAST._IAssignLhs _source86 = lhs;
      if (_source86.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _2582___mcc_h0 = _source86.dtor_ident;
        Dafny.ISequence<Dafny.Rune> _source87 = _2582___mcc_h0;
        Dafny.ISequence<Dafny.Rune> _2583___mcc_h1 = _source87;
        Dafny.ISequence<Dafny.Rune> _2584_id = _2583___mcc_h1;
        {
          Dafny.ISequence<Dafny.Rune> _2585_idRust;
          _2585_idRust = DCOMP.__default.escapeName(_2584_id);
          if (((env).IsBorrowed(_2585_idRust)) || ((env).IsBorrowedMut(_2585_idRust))) {
            generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _2585_idRust), rhs);
          } else {
            generated = RAST.__default.AssignVar(_2585_idRust, rhs);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2585_idRust);
          needsIIFE = false;
        }
      } else if (_source86.is_Select) {
        DAST._IExpression _2586___mcc_h2 = _source86.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _2587___mcc_h3 = _source86.dtor_field;
        Dafny.ISequence<Dafny.Rune> _2588_field = _2587___mcc_h3;
        DAST._IExpression _2589_on = _2586___mcc_h2;
        {
          Dafny.ISequence<Dafny.Rune> _2590_fieldName;
          _2590_fieldName = DCOMP.__default.escapeName(_2588_field);
          RAST._IExpr _2591_onExpr;
          DCOMP._IOwnership _2592_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2593_recIdents;
          RAST._IExpr _out110;
          DCOMP._IOwnership _out111;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out112;
          (this).GenExpr(_2589_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out110, out _out111, out _out112);
          _2591_onExpr = _out110;
          _2592_onOwned = _out111;
          _2593_recIdents = _out112;
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*("), (_2591_onExpr)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _2590_fieldName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()) = ")), (rhs)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";")));
          readIdents = _2593_recIdents;
          needsIIFE = true;
        }
      } else {
        DAST._IExpression _2594___mcc_h4 = _source86.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _2595___mcc_h5 = _source86.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _2596_indices = _2595___mcc_h5;
        DAST._IExpression _2597_on = _2594___mcc_h4;
        {
          RAST._IExpr _2598_onExpr;
          DCOMP._IOwnership _2599_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2600_recIdents;
          RAST._IExpr _out113;
          DCOMP._IOwnership _out114;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out115;
          (this).GenExpr(_2597_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out113, out _out114, out _out115);
          _2598_onExpr = _out113;
          _2599_onOwned = _out114;
          _2600_recIdents = _out115;
          readIdents = _2600_recIdents;
          Dafny.ISequence<Dafny.Rune> _2601_r;
          _2601_r = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          BigInteger _2602_i;
          _2602_i = BigInteger.Zero;
          while ((_2602_i) < (new BigInteger((_2596_indices).Count))) {
            RAST._IExpr _2603_idx;
            DCOMP._IOwnership _2604___v60;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2605_recIdentsIdx;
            RAST._IExpr _out116;
            DCOMP._IOwnership _out117;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out118;
            (this).GenExpr((_2596_indices).Select(_2602_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out116, out _out117, out _out118);
            _2603_idx = _out116;
            _2604___v60 = _out117;
            _2605_recIdentsIdx = _out118;
            _2601_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2601_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let __idx")), Std.Strings.__default.OfNat(_2602_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = <usize as ::dafny_runtime::NumCast>::from(")), (_2603_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap();\n"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2605_recIdentsIdx);
            _2602_i = (_2602_i) + (BigInteger.One);
          }
          _2601_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2601_r, (_2598_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()"));
          _2602_i = BigInteger.Zero;
          while ((_2602_i) < (new BigInteger((_2596_indices).Count))) {
            _2601_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2601_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[__idx")), Std.Strings.__default.OfNat(_2602_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
            _2602_i = (_2602_i) + (BigInteger.One);
          }
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2601_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), (rhs)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n}")));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source88 = stmt;
      if (_source88.is_DeclareVar) {
        Dafny.ISequence<Dafny.Rune> _2606___mcc_h0 = _source88.dtor_name;
        DAST._IType _2607___mcc_h1 = _source88.dtor_typ;
        Std.Wrappers._IOption<DAST._IExpression> _2608___mcc_h2 = _source88.dtor_maybeValue;
        Std.Wrappers._IOption<DAST._IExpression> _source89 = _2608___mcc_h2;
        if (_source89.is_None) {
          DAST._IType _2609_typ = _2607___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _2610_name = _2606___mcc_h0;
          {
            DAST._IStatement _2611_newStmt;
            _2611_newStmt = DAST.Statement.create_DeclareVar(_2610_name, _2609_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_2609_typ)));
            RAST._IExpr _out119;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out120;
            DCOMP._IEnvironment _out121;
            (this).GenStmt(_2611_newStmt, selfIdent, env, isLast, earlyReturn, out _out119, out _out120, out _out121);
            generated = _out119;
            readIdents = _out120;
            newEnv = _out121;
          }
        } else {
          DAST._IExpression _2612___mcc_h3 = _source89.dtor_value;
          DAST._IExpression _2613_expression = _2612___mcc_h3;
          DAST._IType _2614_typ = _2607___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _2615_name = _2606___mcc_h0;
          {
            RAST._IType _2616_tpe;
            RAST._IType _out122;
            _out122 = (this).GenType(_2614_typ, true, false);
            _2616_tpe = _out122;
            RAST._IExpr _2617_expr;
            DCOMP._IOwnership _2618_exprOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2619_recIdents;
            RAST._IExpr _out123;
            DCOMP._IOwnership _out124;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out125;
            (this).GenExpr(_2613_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out123, out _out124, out _out125);
            _2617_expr = _out123;
            _2618_exprOwnership = _out124;
            _2619_recIdents = _out125;
            readIdents = _2619_recIdents;
            generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_2615_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2616_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2617_expr));
            newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_2615_name), _2616_tpe);
          }
        }
      } else if (_source88.is_Assign) {
        DAST._IAssignLhs _2620___mcc_h4 = _source88.dtor_lhs;
        DAST._IExpression _2621___mcc_h5 = _source88.dtor_value;
        DAST._IExpression _2622_expression = _2621___mcc_h5;
        DAST._IAssignLhs _2623_lhs = _2620___mcc_h4;
        {
          RAST._IExpr _2624_exprGen;
          DCOMP._IOwnership _2625___v61;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2626_exprIdents;
          RAST._IExpr _out126;
          DCOMP._IOwnership _out127;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out128;
          (this).GenExpr(_2622_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out126, out _out127, out _out128);
          _2624_exprGen = _out126;
          _2625___v61 = _out127;
          _2626_exprIdents = _out128;
          if ((_2623_lhs).is_Ident) {
            Dafny.ISequence<Dafny.Rune> _2627_rustId;
            _2627_rustId = DCOMP.__default.escapeName(((_2623_lhs).dtor_ident));
            Std.Wrappers._IOption<RAST._IType> _2628_tpe;
            _2628_tpe = (env).GetType(_2627_rustId);
          }
          RAST._IExpr _2629_lhsGen;
          bool _2630_needsIIFE;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2631_recIdents;
          DCOMP._IEnvironment _2632_resEnv;
          RAST._IExpr _out129;
          bool _out130;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
          DCOMP._IEnvironment _out132;
          (this).GenAssignLhs(_2623_lhs, _2624_exprGen, selfIdent, env, out _out129, out _out130, out _out131, out _out132);
          _2629_lhsGen = _out129;
          _2630_needsIIFE = _out130;
          _2631_recIdents = _out131;
          _2632_resEnv = _out132;
          generated = _2629_lhsGen;
          newEnv = _2632_resEnv;
          if (_2630_needsIIFE) {
            generated = RAST.Expr.create_Block(generated);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2631_recIdents, _2626_exprIdents);
        }
      } else if (_source88.is_If) {
        DAST._IExpression _2633___mcc_h6 = _source88.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _2634___mcc_h7 = _source88.dtor_thn;
        Dafny.ISequence<DAST._IStatement> _2635___mcc_h8 = _source88.dtor_els;
        Dafny.ISequence<DAST._IStatement> _2636_elsDafny = _2635___mcc_h8;
        Dafny.ISequence<DAST._IStatement> _2637_thnDafny = _2634___mcc_h7;
        DAST._IExpression _2638_cond = _2633___mcc_h6;
        {
          RAST._IExpr _2639_cond;
          DCOMP._IOwnership _2640___v62;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2641_recIdents;
          RAST._IExpr _out133;
          DCOMP._IOwnership _out134;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
          (this).GenExpr(_2638_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out133, out _out134, out _out135);
          _2639_cond = _out133;
          _2640___v62 = _out134;
          _2641_recIdents = _out135;
          Dafny.ISequence<Dafny.Rune> _2642_condString;
          _2642_condString = (_2639_cond)._ToString(DCOMP.__default.IND);
          readIdents = _2641_recIdents;
          RAST._IExpr _2643_thn;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2644_thnIdents;
          DCOMP._IEnvironment _2645_thnEnv;
          RAST._IExpr _out136;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
          DCOMP._IEnvironment _out138;
          (this).GenStmts(_2637_thnDafny, selfIdent, env, isLast, earlyReturn, out _out136, out _out137, out _out138);
          _2643_thn = _out136;
          _2644_thnIdents = _out137;
          _2645_thnEnv = _out138;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2644_thnIdents);
          RAST._IExpr _2646_els;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2647_elsIdents;
          DCOMP._IEnvironment _2648_elsEnv;
          RAST._IExpr _out139;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out140;
          DCOMP._IEnvironment _out141;
          (this).GenStmts(_2636_elsDafny, selfIdent, env, isLast, earlyReturn, out _out139, out _out140, out _out141);
          _2646_els = _out139;
          _2647_elsIdents = _out140;
          _2648_elsEnv = _out141;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2647_elsIdents);
          newEnv = env;
          generated = RAST.Expr.create_IfExpr(_2639_cond, _2643_thn, _2646_els);
        }
      } else if (_source88.is_Labeled) {
        Dafny.ISequence<Dafny.Rune> _2649___mcc_h9 = _source88.dtor_lbl;
        Dafny.ISequence<DAST._IStatement> _2650___mcc_h10 = _source88.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2651_body = _2650___mcc_h10;
        Dafny.ISequence<Dafny.Rune> _2652_lbl = _2649___mcc_h9;
        {
          RAST._IExpr _2653_body;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2654_bodyIdents;
          DCOMP._IEnvironment _2655_env2;
          RAST._IExpr _out142;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out143;
          DCOMP._IEnvironment _out144;
          (this).GenStmts(_2651_body, selfIdent, env, isLast, earlyReturn, out _out142, out _out143, out _out144);
          _2653_body = _out142;
          _2654_bodyIdents = _out143;
          _2655_env2 = _out144;
          readIdents = _2654_bodyIdents;
          generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _2652_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_2653_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
          newEnv = env;
        }
      } else if (_source88.is_While) {
        DAST._IExpression _2656___mcc_h11 = _source88.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _2657___mcc_h12 = _source88.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2658_body = _2657___mcc_h12;
        DAST._IExpression _2659_cond = _2656___mcc_h11;
        {
          RAST._IExpr _2660_cond;
          DCOMP._IOwnership _2661___v63;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2662_recIdents;
          RAST._IExpr _out145;
          DCOMP._IOwnership _out146;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out147;
          (this).GenExpr(_2659_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out145, out _out146, out _out147);
          _2660_cond = _out145;
          _2661___v63 = _out146;
          _2662_recIdents = _out147;
          readIdents = _2662_recIdents;
          RAST._IExpr _2663_bodyExpr;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2664_bodyIdents;
          DCOMP._IEnvironment _2665_bodyEnv;
          RAST._IExpr _out148;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out149;
          DCOMP._IEnvironment _out150;
          (this).GenStmts(_2658_body, selfIdent, env, false, earlyReturn, out _out148, out _out149, out _out150);
          _2663_bodyExpr = _out148;
          _2664_bodyIdents = _out149;
          _2665_bodyEnv = _out150;
          newEnv = env;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2664_bodyIdents);
          generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_2660_cond), _2663_bodyExpr);
        }
      } else if (_source88.is_Foreach) {
        Dafny.ISequence<Dafny.Rune> _2666___mcc_h13 = _source88.dtor_boundName;
        DAST._IType _2667___mcc_h14 = _source88.dtor_boundType;
        DAST._IExpression _2668___mcc_h15 = _source88.dtor_over;
        Dafny.ISequence<DAST._IStatement> _2669___mcc_h16 = _source88.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2670_body = _2669___mcc_h16;
        DAST._IExpression _2671_over = _2668___mcc_h15;
        DAST._IType _2672_boundType = _2667___mcc_h14;
        Dafny.ISequence<Dafny.Rune> _2673_boundName = _2666___mcc_h13;
        {
          RAST._IExpr _2674_over;
          DCOMP._IOwnership _2675___v64;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2676_recIdents;
          RAST._IExpr _out151;
          DCOMP._IOwnership _out152;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out153;
          (this).GenExpr(_2671_over, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out151, out _out152, out _out153);
          _2674_over = _out151;
          _2675___v64 = _out152;
          _2676_recIdents = _out153;
          RAST._IType _2677_boundTpe;
          RAST._IType _out154;
          _out154 = (this).GenType(_2672_boundType, false, false);
          _2677_boundTpe = _out154;
          readIdents = _2676_recIdents;
          Dafny.ISequence<Dafny.Rune> _2678_boundRName;
          _2678_boundRName = DCOMP.__default.escapeName(_2673_boundName);
          RAST._IExpr _2679_bodyExpr;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2680_bodyIdents;
          DCOMP._IEnvironment _2681_bodyEnv;
          RAST._IExpr _out155;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
          DCOMP._IEnvironment _out157;
          (this).GenStmts(_2670_body, selfIdent, (env).AddAssigned(_2678_boundRName, _2677_boundTpe), false, earlyReturn, out _out155, out _out156, out _out157);
          _2679_bodyExpr = _out155;
          _2680_bodyIdents = _out156;
          _2681_bodyEnv = _out157;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2680_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2678_boundRName));
          newEnv = env;
          generated = RAST.Expr.create_For(_2678_boundRName, _2674_over, _2679_bodyExpr);
        }
      } else if (_source88.is_Call) {
        DAST._IExpression _2682___mcc_h17 = _source88.dtor_on;
        DAST._ICallName _2683___mcc_h18 = _source88.dtor_callName;
        Dafny.ISequence<DAST._IType> _2684___mcc_h19 = _source88.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _2685___mcc_h20 = _source88.dtor_args;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _2686___mcc_h21 = _source88.dtor_outs;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _2687_maybeOutVars = _2686___mcc_h21;
        Dafny.ISequence<DAST._IExpression> _2688_args = _2685___mcc_h20;
        Dafny.ISequence<DAST._IType> _2689_typeArgs = _2684___mcc_h19;
        DAST._ICallName _2690_name = _2683___mcc_h18;
        DAST._IExpression _2691_on = _2682___mcc_h17;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          RAST._IExpr _2692_onExpr;
          DCOMP._IOwnership _2693___v67;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2694_enclosingIdents;
          RAST._IExpr _out158;
          DCOMP._IOwnership _out159;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out160;
          (this).GenExpr(_2691_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out158, out _out159, out _out160);
          _2692_onExpr = _out158;
          _2693___v67 = _out159;
          _2694_enclosingIdents = _out160;
          Dafny.ISequence<RAST._IType> _2695_typeExprs;
          _2695_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
          if ((new BigInteger((_2689_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _2696_typeI;
            _2696_typeI = BigInteger.Zero;
            Dafny.ISequence<RAST._IType> _2697_typeArgsR;
            _2697_typeArgsR = Dafny.Sequence<RAST._IType>.FromElements();
            while ((_2696_typeI) < (new BigInteger((_2689_typeArgs).Count))) {
              RAST._IType _2698_tpe;
              RAST._IType _out161;
              _out161 = (this).GenType((_2689_typeArgs).Select(_2696_typeI), false, false);
              _2698_tpe = _out161;
              _2697_typeArgsR = Dafny.Sequence<RAST._IType>.Concat(_2697_typeArgsR, Dafny.Sequence<RAST._IType>.FromElements(_2698_tpe));
              _2696_typeI = (_2696_typeI) + (BigInteger.One);
            }
          }
          Dafny.ISequence<RAST._IExpr> _2699_argExprs;
          _2699_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi27 = new BigInteger((_2688_args).Count);
          for (BigInteger _2700_i = BigInteger.Zero; _2700_i < _hi27; _2700_i++) {
            DCOMP._IOwnership _2701_argOwnership;
            _2701_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            if (((_2690_name).is_CallName) && ((_2700_i) < (new BigInteger((((_2690_name).dtor_signature)).Count)))) {
              RAST._IType _2702_tpe;
              RAST._IType _out162;
              _out162 = (this).GenType(((((_2690_name).dtor_signature)).Select(_2700_i)).dtor_typ, false, false);
              _2702_tpe = _out162;
              if ((_2702_tpe).CanReadWithoutClone()) {
                _2701_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
              }
            }
            RAST._IExpr _2703_argExpr;
            DCOMP._IOwnership _2704_ownership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2705_argIdents;
            RAST._IExpr _out163;
            DCOMP._IOwnership _out164;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out165;
            (this).GenExpr((_2688_args).Select(_2700_i), selfIdent, env, _2701_argOwnership, out _out163, out _out164, out _out165);
            _2703_argExpr = _out163;
            _2704_ownership = _out164;
            _2705_argIdents = _out165;
            _2699_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_2699_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_2703_argExpr));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2705_argIdents);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2694_enclosingIdents);
          Dafny.ISequence<Dafny.Rune> _2706_renderedName;
          _2706_renderedName = ((System.Func<DAST._ICallName, Dafny.ISequence<Dafny.Rune>>)((_source90) => {
            if (_source90.is_CallName) {
              Dafny.ISequence<Dafny.Rune> _2707___mcc_h26 = _source90.dtor_name;
              Std.Wrappers._IOption<DAST._IType> _2708___mcc_h27 = _source90.dtor_onType;
              Dafny.ISequence<DAST._IFormal> _2709___mcc_h28 = _source90.dtor_signature;
              Dafny.ISequence<Dafny.Rune> _2710_name = _2707___mcc_h26;
              return DCOMP.__default.escapeName(_2710_name);
            } else if (_source90.is_MapBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else if (_source90.is_MapBuilderBuild) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            } else if (_source90.is_SetBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            }
          }))(_2690_name);
          DAST._IExpression _source91 = _2691_on;
          if (_source91.is_Literal) {
            DAST._ILiteral _2711___mcc_h29 = _source91.dtor_Literal_i_a0;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _2712___mcc_h31 = _source91.dtor_Ident_i_a0;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2713___mcc_h33 = _source91.dtor_Companion_i_a0;
            {
              _2692_onExpr = (_2692_onExpr).MSel(_2706_renderedName);
            }
          } else if (_source91.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _2714___mcc_h35 = _source91.dtor_Tuple_i_a0;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2715___mcc_h37 = _source91.dtor_path;
            Dafny.ISequence<DAST._IType> _2716___mcc_h38 = _source91.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _2717___mcc_h39 = _source91.dtor_args;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _2718___mcc_h43 = _source91.dtor_dims;
            DAST._IType _2719___mcc_h44 = _source91.dtor_typ;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_DatatypeValue) {
            DAST._IDatatypeType _2720___mcc_h47 = _source91.dtor_datatypeType;
            Dafny.ISequence<DAST._IType> _2721___mcc_h48 = _source91.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _2722___mcc_h49 = _source91.dtor_variant;
            bool _2723___mcc_h50 = _source91.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2724___mcc_h51 = _source91.dtor_contents;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_Convert) {
            DAST._IExpression _2725___mcc_h57 = _source91.dtor_value;
            DAST._IType _2726___mcc_h58 = _source91.dtor_from;
            DAST._IType _2727___mcc_h59 = _source91.dtor_typ;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_SeqConstruct) {
            DAST._IExpression _2728___mcc_h63 = _source91.dtor_length;
            DAST._IExpression _2729___mcc_h64 = _source91.dtor_elem;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _2730___mcc_h67 = _source91.dtor_elements;
            DAST._IType _2731___mcc_h68 = _source91.dtor_typ;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _2732___mcc_h71 = _source91.dtor_elements;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_MultisetValue) {
            Dafny.ISequence<DAST._IExpression> _2733___mcc_h73 = _source91.dtor_elements;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_MapValue) {
            Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2734___mcc_h75 = _source91.dtor_mapElems;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_MapBuilder) {
            DAST._IType _2735___mcc_h77 = _source91.dtor_keyType;
            DAST._IType _2736___mcc_h78 = _source91.dtor_valueType;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_SeqUpdate) {
            DAST._IExpression _2737___mcc_h81 = _source91.dtor_expr;
            DAST._IExpression _2738___mcc_h82 = _source91.dtor_indexExpr;
            DAST._IExpression _2739___mcc_h83 = _source91.dtor_value;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_MapUpdate) {
            DAST._IExpression _2740___mcc_h87 = _source91.dtor_expr;
            DAST._IExpression _2741___mcc_h88 = _source91.dtor_indexExpr;
            DAST._IExpression _2742___mcc_h89 = _source91.dtor_value;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_SetBuilder) {
            DAST._IType _2743___mcc_h93 = _source91.dtor_elemType;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_ToMultiset) {
            DAST._IExpression _2744___mcc_h95 = _source91.dtor_ToMultiset_i_a0;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_This) {
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_Ite) {
            DAST._IExpression _2745___mcc_h97 = _source91.dtor_cond;
            DAST._IExpression _2746___mcc_h98 = _source91.dtor_thn;
            DAST._IExpression _2747___mcc_h99 = _source91.dtor_els;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_UnOp) {
            DAST._IUnaryOp _2748___mcc_h103 = _source91.dtor_unOp;
            DAST._IExpression _2749___mcc_h104 = _source91.dtor_expr;
            DAST.Format._IUnaryOpFormat _2750___mcc_h105 = _source91.dtor_format1;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_BinOp) {
            DAST._IBinOp _2751___mcc_h109 = _source91.dtor_op;
            DAST._IExpression _2752___mcc_h110 = _source91.dtor_left;
            DAST._IExpression _2753___mcc_h111 = _source91.dtor_right;
            DAST.Format._IBinaryOpFormat _2754___mcc_h112 = _source91.dtor_format2;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_ArrayLen) {
            DAST._IExpression _2755___mcc_h117 = _source91.dtor_expr;
            BigInteger _2756___mcc_h118 = _source91.dtor_dim;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_MapKeys) {
            DAST._IExpression _2757___mcc_h121 = _source91.dtor_expr;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_MapValues) {
            DAST._IExpression _2758___mcc_h123 = _source91.dtor_expr;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_Select) {
            DAST._IExpression _2759___mcc_h125 = _source91.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2760___mcc_h126 = _source91.dtor_field;
            bool _2761___mcc_h127 = _source91.dtor_isConstant;
            bool _2762___mcc_h128 = _source91.dtor_onDatatype;
            DAST._IType _2763___mcc_h129 = _source91.dtor_fieldType;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_SelectFn) {
            DAST._IExpression _2764___mcc_h135 = _source91.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2765___mcc_h136 = _source91.dtor_field;
            bool _2766___mcc_h137 = _source91.dtor_onDatatype;
            bool _2767___mcc_h138 = _source91.dtor_isStatic;
            BigInteger _2768___mcc_h139 = _source91.dtor_arity;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_Index) {
            DAST._IExpression _2769___mcc_h145 = _source91.dtor_expr;
            DAST._ICollKind _2770___mcc_h146 = _source91.dtor_collKind;
            Dafny.ISequence<DAST._IExpression> _2771___mcc_h147 = _source91.dtor_indices;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_IndexRange) {
            DAST._IExpression _2772___mcc_h151 = _source91.dtor_expr;
            bool _2773___mcc_h152 = _source91.dtor_isArray;
            Std.Wrappers._IOption<DAST._IExpression> _2774___mcc_h153 = _source91.dtor_low;
            Std.Wrappers._IOption<DAST._IExpression> _2775___mcc_h154 = _source91.dtor_high;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_TupleSelect) {
            DAST._IExpression _2776___mcc_h159 = _source91.dtor_expr;
            BigInteger _2777___mcc_h160 = _source91.dtor_index;
            DAST._IType _2778___mcc_h161 = _source91.dtor_fieldType;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_Call) {
            DAST._IExpression _2779___mcc_h165 = _source91.dtor_on;
            DAST._ICallName _2780___mcc_h166 = _source91.dtor_callName;
            Dafny.ISequence<DAST._IType> _2781___mcc_h167 = _source91.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _2782___mcc_h168 = _source91.dtor_args;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2783___mcc_h173 = _source91.dtor_params;
            DAST._IType _2784___mcc_h174 = _source91.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _2785___mcc_h175 = _source91.dtor_body;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2786___mcc_h179 = _source91.dtor_values;
            DAST._IType _2787___mcc_h180 = _source91.dtor_retType;
            DAST._IExpression _2788___mcc_h181 = _source91.dtor_expr;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _2789___mcc_h185 = _source91.dtor_name;
            DAST._IType _2790___mcc_h186 = _source91.dtor_typ;
            DAST._IExpression _2791___mcc_h187 = _source91.dtor_value;
            DAST._IExpression _2792___mcc_h188 = _source91.dtor_iifeBody;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_Apply) {
            DAST._IExpression _2793___mcc_h193 = _source91.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _2794___mcc_h194 = _source91.dtor_args;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_TypeTest) {
            DAST._IExpression _2795___mcc_h197 = _source91.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2796___mcc_h198 = _source91.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _2797___mcc_h199 = _source91.dtor_variant;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_InitializationValue) {
            DAST._IType _2798___mcc_h203 = _source91.dtor_typ;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_BoolBoundedPool) {
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_SetBoundedPool) {
            DAST._IExpression _2799___mcc_h205 = _source91.dtor_of;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else if (_source91.is_SeqBoundedPool) {
            DAST._IExpression _2800___mcc_h207 = _source91.dtor_of;
            bool _2801___mcc_h208 = _source91.dtor_includeDuplicates;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          } else {
            DAST._IExpression _2802___mcc_h211 = _source91.dtor_lo;
            DAST._IExpression _2803___mcc_h212 = _source91.dtor_hi;
            {
              _2692_onExpr = (_2692_onExpr).Sel(_2706_renderedName);
            }
          }
          generated = _2692_onExpr;
          if ((new BigInteger((_2695_typeExprs).Count)).Sign == 1) {
            generated = (generated).ApplyType(_2695_typeExprs);
          }
          generated = (generated).Apply(_2699_argExprs);
          if (((_2687_maybeOutVars).is_Some) && ((new BigInteger(((_2687_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
            Dafny.ISequence<Dafny.Rune> _2804_outVar;
            _2804_outVar = DCOMP.__default.escapeName((((_2687_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
            generated = RAST.__default.AssignVar(_2804_outVar, generated);
          } else if (((_2687_maybeOutVars).is_None) || ((new BigInteger(((_2687_maybeOutVars).dtor_value).Count)).Sign == 0)) {
          } else {
            Dafny.ISequence<Dafny.Rune> _2805_tmpVar;
            _2805_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
            RAST._IExpr _2806_tmpId;
            _2806_tmpId = RAST.Expr.create_Identifier(_2805_tmpVar);
            generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _2805_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2807_outVars;
            _2807_outVars = (_2687_maybeOutVars).dtor_value;
            BigInteger _hi28 = new BigInteger((_2807_outVars).Count);
            for (BigInteger _2808_outI = BigInteger.Zero; _2808_outI < _hi28; _2808_outI++) {
              Dafny.ISequence<Dafny.Rune> _2809_outVar;
              _2809_outVar = DCOMP.__default.escapeName(((_2807_outVars).Select(_2808_outI)));
              RAST._IExpr _2810_rhs;
              _2810_rhs = (_2806_tmpId).Sel(Std.Strings.__default.OfNat(_2808_outI));
              generated = (generated).Then(RAST.__default.AssignVar(_2809_outVar, _2810_rhs));
            }
          }
          newEnv = env;
        }
      } else if (_source88.is_Return) {
        DAST._IExpression _2811___mcc_h22 = _source88.dtor_expr;
        DAST._IExpression _2812_exprDafny = _2811___mcc_h22;
        {
          RAST._IExpr _2813_expr;
          DCOMP._IOwnership _2814___v72;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2815_recIdents;
          RAST._IExpr _out166;
          DCOMP._IOwnership _out167;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out168;
          (this).GenExpr(_2812_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out166, out _out167, out _out168);
          _2813_expr = _out166;
          _2814___v72 = _out167;
          _2815_recIdents = _out168;
          readIdents = _2815_recIdents;
          if (isLast) {
            generated = _2813_expr;
          } else {
            generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_2813_expr));
          }
          newEnv = env;
        }
      } else if (_source88.is_EarlyReturn) {
        {
          generated = earlyReturn;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
      } else if (_source88.is_Break) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2816___mcc_h23 = _source88.dtor_toLabel;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2817_toLabel = _2816___mcc_h23;
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source92 = _2817_toLabel;
          if (_source92.is_None) {
            {
              generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2818___mcc_h215 = _source92.dtor_value;
            Dafny.ISequence<Dafny.Rune> _2819_lbl = _2818___mcc_h215;
            {
              generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _2819_lbl)));
            }
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
      } else if (_source88.is_TailRecursive) {
        Dafny.ISequence<DAST._IStatement> _2820___mcc_h24 = _source88.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2821_body = _2820___mcc_h24;
        {
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
            generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
          }
          newEnv = env;
          BigInteger _hi29 = new BigInteger(((env).dtor_names).Count);
          for (BigInteger _2822_paramI = BigInteger.Zero; _2822_paramI < _hi29; _2822_paramI++) {
            Dafny.ISequence<Dafny.Rune> _2823_param;
            _2823_param = ((env).dtor_names).Select(_2822_paramI);
            RAST._IExpr _2824_paramInit;
            DCOMP._IOwnership _2825___v65;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2826___v66;
            RAST._IExpr _out169;
            DCOMP._IOwnership _out170;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out171;
            (this).GenIdent(_2823_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out169, out _out170, out _out171);
            _2824_paramInit = _out169;
            _2825___v65 = _out170;
            _2826___v66 = _out171;
            generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2823_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2824_paramInit)));
            if (((env).dtor_types).Contains(_2823_param)) {
              RAST._IType _2827_declaredType;
              _2827_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_2823_param)).ToOwned();
              newEnv = (newEnv).AddAssigned(_2823_param, _2827_declaredType);
            }
          }
          RAST._IExpr _2828_bodyExpr;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2829_bodyIdents;
          DCOMP._IEnvironment _2830_bodyEnv;
          RAST._IExpr _out172;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out173;
          DCOMP._IEnvironment _out174;
          (this).GenStmts(_2821_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), newEnv, false, earlyReturn, out _out172, out _out173, out _out174);
          _2828_bodyExpr = _out172;
          _2829_bodyIdents = _out173;
          _2830_bodyEnv = _out174;
          readIdents = _2829_bodyIdents;
          generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _2828_bodyExpr)));
        }
      } else if (_source88.is_JumpTailCallStart) {
        {
          generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
      } else if (_source88.is_Halt) {
        {
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
      } else {
        DAST._IExpression _2831___mcc_h25 = _source88.dtor_Print_i_a0;
        DAST._IExpression _2832_e = _2831___mcc_h25;
        {
          RAST._IExpr _2833_printedExpr;
          DCOMP._IOwnership _2834_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2835_recIdents;
          RAST._IExpr _out175;
          DCOMP._IOwnership _out176;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
          (this).GenExpr(_2832_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out175, out _out176, out _out177);
          _2833_printedExpr = _out175;
          _2834_recOwnership = _out176;
          _2835_recIdents = _out177;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_2833_printedExpr)));
          readIdents = _2835_recIdents;
          newEnv = env;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source93 = range;
      if (_source93.is_U8) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
      } else if (_source93.is_I8) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
      } else if (_source93.is_U16) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
      } else if (_source93.is_I16) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
      } else if (_source93.is_U32) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
      } else if (_source93.is_I32) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
      } else if (_source93.is_U64) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
      } else if (_source93.is_I64) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
      } else if (_source93.is_U128) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
      } else if (_source93.is_I128) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
      } else if (_source93.is_BigInt) {
        return Std.Wrappers.Option<RAST._IType>.create_None();
      } else {
        return Std.Wrappers.Option<RAST._IType>.create_None();
      }
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
      DAST._IExpression _source94 = e;
      DAST._ILiteral _2836___mcc_h0 = _source94.dtor_Literal_i_a0;
      DAST._ILiteral _source95 = _2836___mcc_h0;
      if (_source95.is_BoolLiteral) {
        bool _2837___mcc_h1 = _source95.dtor_BoolLiteral_i_a0;
        bool _2838_b = _2837___mcc_h1;
        {
          RAST._IExpr _out182;
          DCOMP._IOwnership _out183;
          DCOMP.COMP.FromOwned(RAST.Expr.create_LiteralBool(_2838_b), expectedOwnership, out _out182, out _out183);
          r = _out182;
          resultingOwnership = _out183;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source95.is_IntLiteral) {
        Dafny.ISequence<Dafny.Rune> _2839___mcc_h2 = _source95.dtor_IntLiteral_i_a0;
        DAST._IType _2840___mcc_h3 = _source95.dtor_IntLiteral_i_a1;
        DAST._IType _2841_t = _2840___mcc_h3;
        Dafny.ISequence<Dafny.Rune> _2842_i = _2839___mcc_h2;
        {
          DAST._IType _source96 = _2841_t;
          if (_source96.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2843___mcc_h102 = _source96.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _2844___mcc_h103 = _source96.dtor_typeArgs;
            DAST._IResolvedType _2845___mcc_h104 = _source96.dtor_resolved;
            DAST._IType _2846_o = _2841_t;
            {
              RAST._IType _2847_genType;
              RAST._IType _out184;
              _out184 = (this).GenType(_2846_o, false, false);
              _2847_genType = _out184;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2842_i), _2847_genType);
            }
          } else if (_source96.is_Nullable) {
            DAST._IType _2848___mcc_h108 = _source96.dtor_Nullable_i_a0;
            DAST._IType _2849_o = _2841_t;
            {
              RAST._IType _2850_genType;
              RAST._IType _out185;
              _out185 = (this).GenType(_2849_o, false, false);
              _2850_genType = _out185;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2842_i), _2850_genType);
            }
          } else if (_source96.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2851___mcc_h110 = _source96.dtor_Tuple_i_a0;
            DAST._IType _2852_o = _2841_t;
            {
              RAST._IType _2853_genType;
              RAST._IType _out186;
              _out186 = (this).GenType(_2852_o, false, false);
              _2853_genType = _out186;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2842_i), _2853_genType);
            }
          } else if (_source96.is_Array) {
            DAST._IType _2854___mcc_h112 = _source96.dtor_element;
            BigInteger _2855___mcc_h113 = _source96.dtor_dims;
            DAST._IType _2856_o = _2841_t;
            {
              RAST._IType _2857_genType;
              RAST._IType _out187;
              _out187 = (this).GenType(_2856_o, false, false);
              _2857_genType = _out187;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2842_i), _2857_genType);
            }
          } else if (_source96.is_Seq) {
            DAST._IType _2858___mcc_h116 = _source96.dtor_element;
            DAST._IType _2859_o = _2841_t;
            {
              RAST._IType _2860_genType;
              RAST._IType _out188;
              _out188 = (this).GenType(_2859_o, false, false);
              _2860_genType = _out188;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2842_i), _2860_genType);
            }
          } else if (_source96.is_Set) {
            DAST._IType _2861___mcc_h118 = _source96.dtor_element;
            DAST._IType _2862_o = _2841_t;
            {
              RAST._IType _2863_genType;
              RAST._IType _out189;
              _out189 = (this).GenType(_2862_o, false, false);
              _2863_genType = _out189;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2842_i), _2863_genType);
            }
          } else if (_source96.is_Multiset) {
            DAST._IType _2864___mcc_h120 = _source96.dtor_element;
            DAST._IType _2865_o = _2841_t;
            {
              RAST._IType _2866_genType;
              RAST._IType _out190;
              _out190 = (this).GenType(_2865_o, false, false);
              _2866_genType = _out190;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2842_i), _2866_genType);
            }
          } else if (_source96.is_Map) {
            DAST._IType _2867___mcc_h122 = _source96.dtor_key;
            DAST._IType _2868___mcc_h123 = _source96.dtor_value;
            DAST._IType _2869_o = _2841_t;
            {
              RAST._IType _2870_genType;
              RAST._IType _out191;
              _out191 = (this).GenType(_2869_o, false, false);
              _2870_genType = _out191;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2842_i), _2870_genType);
            }
          } else if (_source96.is_SetBuilder) {
            DAST._IType _2871___mcc_h126 = _source96.dtor_element;
            DAST._IType _2872_o = _2841_t;
            {
              RAST._IType _2873_genType;
              RAST._IType _out192;
              _out192 = (this).GenType(_2872_o, false, false);
              _2873_genType = _out192;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2842_i), _2873_genType);
            }
          } else if (_source96.is_MapBuilder) {
            DAST._IType _2874___mcc_h128 = _source96.dtor_key;
            DAST._IType _2875___mcc_h129 = _source96.dtor_value;
            DAST._IType _2876_o = _2841_t;
            {
              RAST._IType _2877_genType;
              RAST._IType _out193;
              _out193 = (this).GenType(_2876_o, false, false);
              _2877_genType = _out193;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2842_i), _2877_genType);
            }
          } else if (_source96.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2878___mcc_h132 = _source96.dtor_args;
            DAST._IType _2879___mcc_h133 = _source96.dtor_result;
            DAST._IType _2880_o = _2841_t;
            {
              RAST._IType _2881_genType;
              RAST._IType _out194;
              _out194 = (this).GenType(_2880_o, false, false);
              _2881_genType = _out194;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2842_i), _2881_genType);
            }
          } else if (_source96.is_Primitive) {
            DAST._IPrimitive _2882___mcc_h136 = _source96.dtor_Primitive_i_a0;
            DAST._IPrimitive _source97 = _2882___mcc_h136;
            if (_source97.is_Int) {
              {
                if ((new BigInteger((_2842_i).Count)) <= (new BigInteger(4))) {
                  r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_2842_i));
                } else {
                  r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_2842_i, true));
                }
              }
            } else if (_source97.is_Real) {
              DAST._IType _2883_o = _2841_t;
              {
                RAST._IType _2884_genType;
                RAST._IType _out195;
                _out195 = (this).GenType(_2883_o, false, false);
                _2884_genType = _out195;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2842_i), _2884_genType);
              }
            } else if (_source97.is_String) {
              DAST._IType _2885_o = _2841_t;
              {
                RAST._IType _2886_genType;
                RAST._IType _out196;
                _out196 = (this).GenType(_2885_o, false, false);
                _2886_genType = _out196;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2842_i), _2886_genType);
              }
            } else if (_source97.is_Bool) {
              DAST._IType _2887_o = _2841_t;
              {
                RAST._IType _2888_genType;
                RAST._IType _out197;
                _out197 = (this).GenType(_2887_o, false, false);
                _2888_genType = _out197;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2842_i), _2888_genType);
              }
            } else {
              DAST._IType _2889_o = _2841_t;
              {
                RAST._IType _2890_genType;
                RAST._IType _out198;
                _out198 = (this).GenType(_2889_o, false, false);
                _2890_genType = _out198;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2842_i), _2890_genType);
              }
            }
          } else if (_source96.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2891___mcc_h138 = _source96.dtor_Passthrough_i_a0;
            DAST._IType _2892_o = _2841_t;
            {
              RAST._IType _2893_genType;
              RAST._IType _out199;
              _out199 = (this).GenType(_2892_o, false, false);
              _2893_genType = _out199;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2842_i), _2893_genType);
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2894___mcc_h140 = _source96.dtor_TypeArg_i_a0;
            DAST._IType _2895_o = _2841_t;
            {
              RAST._IType _2896_genType;
              RAST._IType _out200;
              _out200 = (this).GenType(_2895_o, false, false);
              _2896_genType = _out200;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2842_i), _2896_genType);
            }
          }
          RAST._IExpr _out201;
          DCOMP._IOwnership _out202;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out201, out _out202);
          r = _out201;
          resultingOwnership = _out202;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source95.is_DecLiteral) {
        Dafny.ISequence<Dafny.Rune> _2897___mcc_h4 = _source95.dtor_DecLiteral_i_a0;
        Dafny.ISequence<Dafny.Rune> _2898___mcc_h5 = _source95.dtor_DecLiteral_i_a1;
        DAST._IType _2899___mcc_h6 = _source95.dtor_DecLiteral_i_a2;
        DAST._IType _2900_t = _2899___mcc_h6;
        Dafny.ISequence<Dafny.Rune> _2901_d = _2898___mcc_h5;
        Dafny.ISequence<Dafny.Rune> _2902_n = _2897___mcc_h4;
        {
          DAST._IType _source98 = _2900_t;
          if (_source98.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2903___mcc_h142 = _source98.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _2904___mcc_h143 = _source98.dtor_typeArgs;
            DAST._IResolvedType _2905___mcc_h144 = _source98.dtor_resolved;
            DAST._IType _2906_o = _2900_t;
            {
              RAST._IType _2907_genType;
              RAST._IType _out203;
              _out203 = (this).GenType(_2906_o, false, false);
              _2907_genType = _out203;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2902_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2901_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2907_genType);
            }
          } else if (_source98.is_Nullable) {
            DAST._IType _2908___mcc_h148 = _source98.dtor_Nullable_i_a0;
            DAST._IType _2909_o = _2900_t;
            {
              RAST._IType _2910_genType;
              RAST._IType _out204;
              _out204 = (this).GenType(_2909_o, false, false);
              _2910_genType = _out204;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2902_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2901_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2910_genType);
            }
          } else if (_source98.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2911___mcc_h150 = _source98.dtor_Tuple_i_a0;
            DAST._IType _2912_o = _2900_t;
            {
              RAST._IType _2913_genType;
              RAST._IType _out205;
              _out205 = (this).GenType(_2912_o, false, false);
              _2913_genType = _out205;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2902_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2901_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2913_genType);
            }
          } else if (_source98.is_Array) {
            DAST._IType _2914___mcc_h152 = _source98.dtor_element;
            BigInteger _2915___mcc_h153 = _source98.dtor_dims;
            DAST._IType _2916_o = _2900_t;
            {
              RAST._IType _2917_genType;
              RAST._IType _out206;
              _out206 = (this).GenType(_2916_o, false, false);
              _2917_genType = _out206;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2902_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2901_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2917_genType);
            }
          } else if (_source98.is_Seq) {
            DAST._IType _2918___mcc_h156 = _source98.dtor_element;
            DAST._IType _2919_o = _2900_t;
            {
              RAST._IType _2920_genType;
              RAST._IType _out207;
              _out207 = (this).GenType(_2919_o, false, false);
              _2920_genType = _out207;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2902_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2901_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2920_genType);
            }
          } else if (_source98.is_Set) {
            DAST._IType _2921___mcc_h158 = _source98.dtor_element;
            DAST._IType _2922_o = _2900_t;
            {
              RAST._IType _2923_genType;
              RAST._IType _out208;
              _out208 = (this).GenType(_2922_o, false, false);
              _2923_genType = _out208;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2902_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2901_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2923_genType);
            }
          } else if (_source98.is_Multiset) {
            DAST._IType _2924___mcc_h160 = _source98.dtor_element;
            DAST._IType _2925_o = _2900_t;
            {
              RAST._IType _2926_genType;
              RAST._IType _out209;
              _out209 = (this).GenType(_2925_o, false, false);
              _2926_genType = _out209;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2902_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2901_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2926_genType);
            }
          } else if (_source98.is_Map) {
            DAST._IType _2927___mcc_h162 = _source98.dtor_key;
            DAST._IType _2928___mcc_h163 = _source98.dtor_value;
            DAST._IType _2929_o = _2900_t;
            {
              RAST._IType _2930_genType;
              RAST._IType _out210;
              _out210 = (this).GenType(_2929_o, false, false);
              _2930_genType = _out210;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2902_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2901_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2930_genType);
            }
          } else if (_source98.is_SetBuilder) {
            DAST._IType _2931___mcc_h166 = _source98.dtor_element;
            DAST._IType _2932_o = _2900_t;
            {
              RAST._IType _2933_genType;
              RAST._IType _out211;
              _out211 = (this).GenType(_2932_o, false, false);
              _2933_genType = _out211;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2902_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2901_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2933_genType);
            }
          } else if (_source98.is_MapBuilder) {
            DAST._IType _2934___mcc_h168 = _source98.dtor_key;
            DAST._IType _2935___mcc_h169 = _source98.dtor_value;
            DAST._IType _2936_o = _2900_t;
            {
              RAST._IType _2937_genType;
              RAST._IType _out212;
              _out212 = (this).GenType(_2936_o, false, false);
              _2937_genType = _out212;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2902_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2901_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2937_genType);
            }
          } else if (_source98.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2938___mcc_h172 = _source98.dtor_args;
            DAST._IType _2939___mcc_h173 = _source98.dtor_result;
            DAST._IType _2940_o = _2900_t;
            {
              RAST._IType _2941_genType;
              RAST._IType _out213;
              _out213 = (this).GenType(_2940_o, false, false);
              _2941_genType = _out213;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2902_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2901_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2941_genType);
            }
          } else if (_source98.is_Primitive) {
            DAST._IPrimitive _2942___mcc_h176 = _source98.dtor_Primitive_i_a0;
            DAST._IPrimitive _source99 = _2942___mcc_h176;
            if (_source99.is_Int) {
              DAST._IType _2943_o = _2900_t;
              {
                RAST._IType _2944_genType;
                RAST._IType _out214;
                _out214 = (this).GenType(_2943_o, false, false);
                _2944_genType = _out214;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2902_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2901_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2944_genType);
              }
            } else if (_source99.is_Real) {
              {
                r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _2902_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _2901_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
              }
            } else if (_source99.is_String) {
              DAST._IType _2945_o = _2900_t;
              {
                RAST._IType _2946_genType;
                RAST._IType _out215;
                _out215 = (this).GenType(_2945_o, false, false);
                _2946_genType = _out215;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2902_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2901_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2946_genType);
              }
            } else if (_source99.is_Bool) {
              DAST._IType _2947_o = _2900_t;
              {
                RAST._IType _2948_genType;
                RAST._IType _out216;
                _out216 = (this).GenType(_2947_o, false, false);
                _2948_genType = _out216;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2902_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2901_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2948_genType);
              }
            } else {
              DAST._IType _2949_o = _2900_t;
              {
                RAST._IType _2950_genType;
                RAST._IType _out217;
                _out217 = (this).GenType(_2949_o, false, false);
                _2950_genType = _out217;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2902_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2901_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2950_genType);
              }
            }
          } else if (_source98.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2951___mcc_h178 = _source98.dtor_Passthrough_i_a0;
            DAST._IType _2952_o = _2900_t;
            {
              RAST._IType _2953_genType;
              RAST._IType _out218;
              _out218 = (this).GenType(_2952_o, false, false);
              _2953_genType = _out218;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2902_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2901_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2953_genType);
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2954___mcc_h180 = _source98.dtor_TypeArg_i_a0;
            DAST._IType _2955_o = _2900_t;
            {
              RAST._IType _2956_genType;
              RAST._IType _out219;
              _out219 = (this).GenType(_2955_o, false, false);
              _2956_genType = _out219;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2902_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2901_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2956_genType);
            }
          }
          RAST._IExpr _out220;
          DCOMP._IOwnership _out221;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out220, out _out221);
          r = _out220;
          resultingOwnership = _out221;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source95.is_StringLiteral) {
        Dafny.ISequence<Dafny.Rune> _2957___mcc_h7 = _source95.dtor_StringLiteral_i_a0;
        Dafny.ISequence<Dafny.Rune> _2958_l = _2957___mcc_h7;
        {
          r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_2958_l, false));
          RAST._IExpr _out222;
          DCOMP._IOwnership _out223;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out222, out _out223);
          r = _out222;
          resultingOwnership = _out223;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source95.is_CharLiteral) {
        Dafny.Rune _2959___mcc_h8 = _source95.dtor_CharLiteral_i_a0;
        Dafny.Rune _2960_c = _2959___mcc_h8;
        {
          r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_2960_c).Value)));
          if (!((this).UnicodeChars)) {
            r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
          } else {
            r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          }
          r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
          RAST._IExpr _out224;
          DCOMP._IOwnership _out225;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out224, out _out225);
          r = _out224;
          resultingOwnership = _out225;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else {
        DAST._IType _2961___mcc_h9 = _source95.dtor_Null_i_a0;
        DAST._IType _2962_tpe = _2961___mcc_h9;
        {
          RAST._IType _2963_tpeGen;
          RAST._IType _out226;
          _out226 = (this).GenType(_2962_tpe, false, false);
          _2963_tpeGen = _out226;
          r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None")), _2963_tpeGen);
          RAST._IExpr _out227;
          DCOMP._IOwnership _out228;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out227, out _out228);
          r = _out227;
          resultingOwnership = _out228;
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
      DAST._IBinOp _2964_op = _let_tmp_rhs52.dtor_op;
      DAST._IExpression _2965_lExpr = _let_tmp_rhs52.dtor_left;
      DAST._IExpression _2966_rExpr = _let_tmp_rhs52.dtor_right;
      DAST.Format._IBinaryOpFormat _2967_format = _let_tmp_rhs52.dtor_format2;
      bool _2968_becomesLeftCallsRight;
      _2968_becomesLeftCallsRight = ((System.Func<DAST._IBinOp, bool>)((_source100) => {
        if (_source100.is_Eq) {
          bool _2969___mcc_h0 = _source100.dtor_referential;
          bool _2970___mcc_h1 = _source100.dtor_nullable;
          return false;
        } else if (_source100.is_Div) {
          return false;
        } else if (_source100.is_EuclidianDiv) {
          return false;
        } else if (_source100.is_Mod) {
          return false;
        } else if (_source100.is_EuclidianMod) {
          return false;
        } else if (_source100.is_Lt) {
          return false;
        } else if (_source100.is_LtChar) {
          return false;
        } else if (_source100.is_Plus) {
          return false;
        } else if (_source100.is_Minus) {
          return false;
        } else if (_source100.is_Times) {
          return false;
        } else if (_source100.is_BitwiseAnd) {
          return false;
        } else if (_source100.is_BitwiseOr) {
          return false;
        } else if (_source100.is_BitwiseXor) {
          return false;
        } else if (_source100.is_BitwiseShiftRight) {
          return false;
        } else if (_source100.is_BitwiseShiftLeft) {
          return false;
        } else if (_source100.is_And) {
          return false;
        } else if (_source100.is_Or) {
          return false;
        } else if (_source100.is_In) {
          return false;
        } else if (_source100.is_SeqProperPrefix) {
          return false;
        } else if (_source100.is_SeqPrefix) {
          return false;
        } else if (_source100.is_SetMerge) {
          return true;
        } else if (_source100.is_SetSubtraction) {
          return true;
        } else if (_source100.is_SetIntersection) {
          return true;
        } else if (_source100.is_Subset) {
          return false;
        } else if (_source100.is_ProperSubset) {
          return false;
        } else if (_source100.is_SetDisjoint) {
          return true;
        } else if (_source100.is_MapMerge) {
          return true;
        } else if (_source100.is_MapSubtraction) {
          return true;
        } else if (_source100.is_MultisetMerge) {
          return true;
        } else if (_source100.is_MultisetSubtraction) {
          return true;
        } else if (_source100.is_MultisetIntersection) {
          return true;
        } else if (_source100.is_Submultiset) {
          return false;
        } else if (_source100.is_ProperSubmultiset) {
          return false;
        } else if (_source100.is_MultisetDisjoint) {
          return true;
        } else if (_source100.is_Concat) {
          return true;
        } else {
          Dafny.ISequence<Dafny.Rune> _2971___mcc_h4 = _source100.dtor_Passthrough_i_a0;
          return false;
        }
      }))(_2964_op);
      bool _2972_becomesRightCallsLeft;
      _2972_becomesRightCallsLeft = ((System.Func<DAST._IBinOp, bool>)((_source101) => {
        if (_source101.is_Eq) {
          bool _2973___mcc_h6 = _source101.dtor_referential;
          bool _2974___mcc_h7 = _source101.dtor_nullable;
          return false;
        } else if (_source101.is_Div) {
          return false;
        } else if (_source101.is_EuclidianDiv) {
          return false;
        } else if (_source101.is_Mod) {
          return false;
        } else if (_source101.is_EuclidianMod) {
          return false;
        } else if (_source101.is_Lt) {
          return false;
        } else if (_source101.is_LtChar) {
          return false;
        } else if (_source101.is_Plus) {
          return false;
        } else if (_source101.is_Minus) {
          return false;
        } else if (_source101.is_Times) {
          return false;
        } else if (_source101.is_BitwiseAnd) {
          return false;
        } else if (_source101.is_BitwiseOr) {
          return false;
        } else if (_source101.is_BitwiseXor) {
          return false;
        } else if (_source101.is_BitwiseShiftRight) {
          return false;
        } else if (_source101.is_BitwiseShiftLeft) {
          return false;
        } else if (_source101.is_And) {
          return false;
        } else if (_source101.is_Or) {
          return false;
        } else if (_source101.is_In) {
          return true;
        } else if (_source101.is_SeqProperPrefix) {
          return false;
        } else if (_source101.is_SeqPrefix) {
          return false;
        } else if (_source101.is_SetMerge) {
          return false;
        } else if (_source101.is_SetSubtraction) {
          return false;
        } else if (_source101.is_SetIntersection) {
          return false;
        } else if (_source101.is_Subset) {
          return false;
        } else if (_source101.is_ProperSubset) {
          return false;
        } else if (_source101.is_SetDisjoint) {
          return false;
        } else if (_source101.is_MapMerge) {
          return false;
        } else if (_source101.is_MapSubtraction) {
          return false;
        } else if (_source101.is_MultisetMerge) {
          return false;
        } else if (_source101.is_MultisetSubtraction) {
          return false;
        } else if (_source101.is_MultisetIntersection) {
          return false;
        } else if (_source101.is_Submultiset) {
          return false;
        } else if (_source101.is_ProperSubmultiset) {
          return false;
        } else if (_source101.is_MultisetDisjoint) {
          return false;
        } else if (_source101.is_Concat) {
          return false;
        } else {
          Dafny.ISequence<Dafny.Rune> _2975___mcc_h10 = _source101.dtor_Passthrough_i_a0;
          return false;
        }
      }))(_2964_op);
      bool _2976_becomesCallLeftRight;
      _2976_becomesCallLeftRight = ((System.Func<DAST._IBinOp, bool>)((_source102) => {
        if (_source102.is_Eq) {
          bool _2977___mcc_h12 = _source102.dtor_referential;
          bool _2978___mcc_h13 = _source102.dtor_nullable;
          if ((_2977___mcc_h12) == (true)) {
            if ((_2978___mcc_h13) == (false)) {
              return true;
            } else {
              return false;
            }
          } else {
            return false;
          }
        } else if (_source102.is_Div) {
          return false;
        } else if (_source102.is_EuclidianDiv) {
          return false;
        } else if (_source102.is_Mod) {
          return false;
        } else if (_source102.is_EuclidianMod) {
          return false;
        } else if (_source102.is_Lt) {
          return false;
        } else if (_source102.is_LtChar) {
          return false;
        } else if (_source102.is_Plus) {
          return false;
        } else if (_source102.is_Minus) {
          return false;
        } else if (_source102.is_Times) {
          return false;
        } else if (_source102.is_BitwiseAnd) {
          return false;
        } else if (_source102.is_BitwiseOr) {
          return false;
        } else if (_source102.is_BitwiseXor) {
          return false;
        } else if (_source102.is_BitwiseShiftRight) {
          return false;
        } else if (_source102.is_BitwiseShiftLeft) {
          return false;
        } else if (_source102.is_And) {
          return false;
        } else if (_source102.is_Or) {
          return false;
        } else if (_source102.is_In) {
          return false;
        } else if (_source102.is_SeqProperPrefix) {
          return false;
        } else if (_source102.is_SeqPrefix) {
          return false;
        } else if (_source102.is_SetMerge) {
          return true;
        } else if (_source102.is_SetSubtraction) {
          return true;
        } else if (_source102.is_SetIntersection) {
          return true;
        } else if (_source102.is_Subset) {
          return false;
        } else if (_source102.is_ProperSubset) {
          return false;
        } else if (_source102.is_SetDisjoint) {
          return true;
        } else if (_source102.is_MapMerge) {
          return true;
        } else if (_source102.is_MapSubtraction) {
          return true;
        } else if (_source102.is_MultisetMerge) {
          return true;
        } else if (_source102.is_MultisetSubtraction) {
          return true;
        } else if (_source102.is_MultisetIntersection) {
          return true;
        } else if (_source102.is_Submultiset) {
          return false;
        } else if (_source102.is_ProperSubmultiset) {
          return false;
        } else if (_source102.is_MultisetDisjoint) {
          return true;
        } else if (_source102.is_Concat) {
          return true;
        } else {
          Dafny.ISequence<Dafny.Rune> _2979___mcc_h16 = _source102.dtor_Passthrough_i_a0;
          return false;
        }
      }))(_2964_op);
      DCOMP._IOwnership _2980_expectedLeftOwnership;
      _2980_expectedLeftOwnership = ((_2968_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_2972_becomesRightCallsLeft) || (_2976_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _2981_expectedRightOwnership;
      _2981_expectedRightOwnership = (((_2968_becomesLeftCallsRight) || (_2976_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_2972_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _2982_left;
      DCOMP._IOwnership _2983___v77;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2984_recIdentsL;
      RAST._IExpr _out229;
      DCOMP._IOwnership _out230;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out231;
      (this).GenExpr(_2965_lExpr, selfIdent, env, _2980_expectedLeftOwnership, out _out229, out _out230, out _out231);
      _2982_left = _out229;
      _2983___v77 = _out230;
      _2984_recIdentsL = _out231;
      RAST._IExpr _2985_right;
      DCOMP._IOwnership _2986___v78;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2987_recIdentsR;
      RAST._IExpr _out232;
      DCOMP._IOwnership _out233;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out234;
      (this).GenExpr(_2966_rExpr, selfIdent, env, _2981_expectedRightOwnership, out _out232, out _out233, out _out234);
      _2985_right = _out232;
      _2986___v78 = _out233;
      _2987_recIdentsR = _out234;
      DAST._IBinOp _source103 = _2964_op;
      if (_source103.is_Eq) {
        bool _2988___mcc_h18 = _source103.dtor_referential;
        bool _2989___mcc_h19 = _source103.dtor_nullable;
        {
          if ((DCOMP.COMP.OpTable).Contains(_2964_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2964_op), _2982_left, _2985_right, _2967_format);
          } else {
            DAST._IBinOp _source104 = _2964_op;
            if (_source104.is_Eq) {
              bool _2990___mcc_h24 = _source104.dtor_referential;
              bool _2991___mcc_h25 = _source104.dtor_nullable;
              bool _2992_nullable = _2991___mcc_h25;
              bool _2993_referential = _2990___mcc_h24;
              {
                if (_2993_referential) {
                  if (_2992_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2982_left, _2985_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source104.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else if (_source104.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2994___mcc_h26 = _source104.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _2995_op = _2994___mcc_h26;
              {
                r = RAST.Expr.create_BinaryOp(_2995_op, _2982_left, _2985_right, _2967_format);
              }
            }
          }
        }
      } else if (_source103.is_Div) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2964_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2964_op), _2982_left, _2985_right, _2967_format);
          } else {
            DAST._IBinOp _source105 = _2964_op;
            if (_source105.is_Eq) {
              bool _2996___mcc_h27 = _source105.dtor_referential;
              bool _2997___mcc_h28 = _source105.dtor_nullable;
              bool _2998_nullable = _2997___mcc_h28;
              bool _2999_referential = _2996___mcc_h27;
              {
                if (_2999_referential) {
                  if (_2998_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2982_left, _2985_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source105.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else if (_source105.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3000___mcc_h29 = _source105.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3001_op = _3000___mcc_h29;
              {
                r = RAST.Expr.create_BinaryOp(_3001_op, _2982_left, _2985_right, _2967_format);
              }
            }
          }
        }
      } else if (_source103.is_EuclidianDiv) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2964_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2964_op), _2982_left, _2985_right, _2967_format);
          } else {
            DAST._IBinOp _source106 = _2964_op;
            if (_source106.is_Eq) {
              bool _3002___mcc_h30 = _source106.dtor_referential;
              bool _3003___mcc_h31 = _source106.dtor_nullable;
              bool _3004_nullable = _3003___mcc_h31;
              bool _3005_referential = _3002___mcc_h30;
              {
                if (_3005_referential) {
                  if (_3004_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2982_left, _2985_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source106.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else if (_source106.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3006___mcc_h32 = _source106.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3007_op = _3006___mcc_h32;
              {
                r = RAST.Expr.create_BinaryOp(_3007_op, _2982_left, _2985_right, _2967_format);
              }
            }
          }
        }
      } else if (_source103.is_Mod) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2964_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2964_op), _2982_left, _2985_right, _2967_format);
          } else {
            DAST._IBinOp _source107 = _2964_op;
            if (_source107.is_Eq) {
              bool _3008___mcc_h33 = _source107.dtor_referential;
              bool _3009___mcc_h34 = _source107.dtor_nullable;
              bool _3010_nullable = _3009___mcc_h34;
              bool _3011_referential = _3008___mcc_h33;
              {
                if (_3011_referential) {
                  if (_3010_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2982_left, _2985_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source107.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else if (_source107.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3012___mcc_h35 = _source107.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3013_op = _3012___mcc_h35;
              {
                r = RAST.Expr.create_BinaryOp(_3013_op, _2982_left, _2985_right, _2967_format);
              }
            }
          }
        }
      } else if (_source103.is_EuclidianMod) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2964_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2964_op), _2982_left, _2985_right, _2967_format);
          } else {
            DAST._IBinOp _source108 = _2964_op;
            if (_source108.is_Eq) {
              bool _3014___mcc_h36 = _source108.dtor_referential;
              bool _3015___mcc_h37 = _source108.dtor_nullable;
              bool _3016_nullable = _3015___mcc_h37;
              bool _3017_referential = _3014___mcc_h36;
              {
                if (_3017_referential) {
                  if (_3016_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2982_left, _2985_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source108.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else if (_source108.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3018___mcc_h38 = _source108.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3019_op = _3018___mcc_h38;
              {
                r = RAST.Expr.create_BinaryOp(_3019_op, _2982_left, _2985_right, _2967_format);
              }
            }
          }
        }
      } else if (_source103.is_Lt) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2964_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2964_op), _2982_left, _2985_right, _2967_format);
          } else {
            DAST._IBinOp _source109 = _2964_op;
            if (_source109.is_Eq) {
              bool _3020___mcc_h39 = _source109.dtor_referential;
              bool _3021___mcc_h40 = _source109.dtor_nullable;
              bool _3022_nullable = _3021___mcc_h40;
              bool _3023_referential = _3020___mcc_h39;
              {
                if (_3023_referential) {
                  if (_3022_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2982_left, _2985_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source109.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else if (_source109.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3024___mcc_h41 = _source109.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3025_op = _3024___mcc_h41;
              {
                r = RAST.Expr.create_BinaryOp(_3025_op, _2982_left, _2985_right, _2967_format);
              }
            }
          }
        }
      } else if (_source103.is_LtChar) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2964_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2964_op), _2982_left, _2985_right, _2967_format);
          } else {
            DAST._IBinOp _source110 = _2964_op;
            if (_source110.is_Eq) {
              bool _3026___mcc_h42 = _source110.dtor_referential;
              bool _3027___mcc_h43 = _source110.dtor_nullable;
              bool _3028_nullable = _3027___mcc_h43;
              bool _3029_referential = _3026___mcc_h42;
              {
                if (_3029_referential) {
                  if (_3028_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2982_left, _2985_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source110.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else if (_source110.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3030___mcc_h44 = _source110.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3031_op = _3030___mcc_h44;
              {
                r = RAST.Expr.create_BinaryOp(_3031_op, _2982_left, _2985_right, _2967_format);
              }
            }
          }
        }
      } else if (_source103.is_Plus) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2964_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2964_op), _2982_left, _2985_right, _2967_format);
          } else {
            DAST._IBinOp _source111 = _2964_op;
            if (_source111.is_Eq) {
              bool _3032___mcc_h45 = _source111.dtor_referential;
              bool _3033___mcc_h46 = _source111.dtor_nullable;
              bool _3034_nullable = _3033___mcc_h46;
              bool _3035_referential = _3032___mcc_h45;
              {
                if (_3035_referential) {
                  if (_3034_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2982_left, _2985_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source111.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else if (_source111.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3036___mcc_h47 = _source111.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3037_op = _3036___mcc_h47;
              {
                r = RAST.Expr.create_BinaryOp(_3037_op, _2982_left, _2985_right, _2967_format);
              }
            }
          }
        }
      } else if (_source103.is_Minus) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2964_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2964_op), _2982_left, _2985_right, _2967_format);
          } else {
            DAST._IBinOp _source112 = _2964_op;
            if (_source112.is_Eq) {
              bool _3038___mcc_h48 = _source112.dtor_referential;
              bool _3039___mcc_h49 = _source112.dtor_nullable;
              bool _3040_nullable = _3039___mcc_h49;
              bool _3041_referential = _3038___mcc_h48;
              {
                if (_3041_referential) {
                  if (_3040_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2982_left, _2985_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source112.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else if (_source112.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3042___mcc_h50 = _source112.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3043_op = _3042___mcc_h50;
              {
                r = RAST.Expr.create_BinaryOp(_3043_op, _2982_left, _2985_right, _2967_format);
              }
            }
          }
        }
      } else if (_source103.is_Times) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2964_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2964_op), _2982_left, _2985_right, _2967_format);
          } else {
            DAST._IBinOp _source113 = _2964_op;
            if (_source113.is_Eq) {
              bool _3044___mcc_h51 = _source113.dtor_referential;
              bool _3045___mcc_h52 = _source113.dtor_nullable;
              bool _3046_nullable = _3045___mcc_h52;
              bool _3047_referential = _3044___mcc_h51;
              {
                if (_3047_referential) {
                  if (_3046_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2982_left, _2985_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source113.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else if (_source113.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3048___mcc_h53 = _source113.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3049_op = _3048___mcc_h53;
              {
                r = RAST.Expr.create_BinaryOp(_3049_op, _2982_left, _2985_right, _2967_format);
              }
            }
          }
        }
      } else if (_source103.is_BitwiseAnd) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2964_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2964_op), _2982_left, _2985_right, _2967_format);
          } else {
            DAST._IBinOp _source114 = _2964_op;
            if (_source114.is_Eq) {
              bool _3050___mcc_h54 = _source114.dtor_referential;
              bool _3051___mcc_h55 = _source114.dtor_nullable;
              bool _3052_nullable = _3051___mcc_h55;
              bool _3053_referential = _3050___mcc_h54;
              {
                if (_3053_referential) {
                  if (_3052_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2982_left, _2985_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source114.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else if (_source114.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3054___mcc_h56 = _source114.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3055_op = _3054___mcc_h56;
              {
                r = RAST.Expr.create_BinaryOp(_3055_op, _2982_left, _2985_right, _2967_format);
              }
            }
          }
        }
      } else if (_source103.is_BitwiseOr) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2964_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2964_op), _2982_left, _2985_right, _2967_format);
          } else {
            DAST._IBinOp _source115 = _2964_op;
            if (_source115.is_Eq) {
              bool _3056___mcc_h57 = _source115.dtor_referential;
              bool _3057___mcc_h58 = _source115.dtor_nullable;
              bool _3058_nullable = _3057___mcc_h58;
              bool _3059_referential = _3056___mcc_h57;
              {
                if (_3059_referential) {
                  if (_3058_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2982_left, _2985_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source115.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else if (_source115.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3060___mcc_h59 = _source115.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3061_op = _3060___mcc_h59;
              {
                r = RAST.Expr.create_BinaryOp(_3061_op, _2982_left, _2985_right, _2967_format);
              }
            }
          }
        }
      } else if (_source103.is_BitwiseXor) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2964_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2964_op), _2982_left, _2985_right, _2967_format);
          } else {
            DAST._IBinOp _source116 = _2964_op;
            if (_source116.is_Eq) {
              bool _3062___mcc_h60 = _source116.dtor_referential;
              bool _3063___mcc_h61 = _source116.dtor_nullable;
              bool _3064_nullable = _3063___mcc_h61;
              bool _3065_referential = _3062___mcc_h60;
              {
                if (_3065_referential) {
                  if (_3064_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2982_left, _2985_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source116.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else if (_source116.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3066___mcc_h62 = _source116.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3067_op = _3066___mcc_h62;
              {
                r = RAST.Expr.create_BinaryOp(_3067_op, _2982_left, _2985_right, _2967_format);
              }
            }
          }
        }
      } else if (_source103.is_BitwiseShiftRight) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2964_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2964_op), _2982_left, _2985_right, _2967_format);
          } else {
            DAST._IBinOp _source117 = _2964_op;
            if (_source117.is_Eq) {
              bool _3068___mcc_h63 = _source117.dtor_referential;
              bool _3069___mcc_h64 = _source117.dtor_nullable;
              bool _3070_nullable = _3069___mcc_h64;
              bool _3071_referential = _3068___mcc_h63;
              {
                if (_3071_referential) {
                  if (_3070_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2982_left, _2985_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source117.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else if (_source117.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3072___mcc_h65 = _source117.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3073_op = _3072___mcc_h65;
              {
                r = RAST.Expr.create_BinaryOp(_3073_op, _2982_left, _2985_right, _2967_format);
              }
            }
          }
        }
      } else if (_source103.is_BitwiseShiftLeft) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2964_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2964_op), _2982_left, _2985_right, _2967_format);
          } else {
            DAST._IBinOp _source118 = _2964_op;
            if (_source118.is_Eq) {
              bool _3074___mcc_h66 = _source118.dtor_referential;
              bool _3075___mcc_h67 = _source118.dtor_nullable;
              bool _3076_nullable = _3075___mcc_h67;
              bool _3077_referential = _3074___mcc_h66;
              {
                if (_3077_referential) {
                  if (_3076_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2982_left, _2985_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source118.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else if (_source118.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3078___mcc_h68 = _source118.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3079_op = _3078___mcc_h68;
              {
                r = RAST.Expr.create_BinaryOp(_3079_op, _2982_left, _2985_right, _2967_format);
              }
            }
          }
        }
      } else if (_source103.is_And) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2964_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2964_op), _2982_left, _2985_right, _2967_format);
          } else {
            DAST._IBinOp _source119 = _2964_op;
            if (_source119.is_Eq) {
              bool _3080___mcc_h69 = _source119.dtor_referential;
              bool _3081___mcc_h70 = _source119.dtor_nullable;
              bool _3082_nullable = _3081___mcc_h70;
              bool _3083_referential = _3080___mcc_h69;
              {
                if (_3083_referential) {
                  if (_3082_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2982_left, _2985_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source119.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else if (_source119.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3084___mcc_h71 = _source119.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3085_op = _3084___mcc_h71;
              {
                r = RAST.Expr.create_BinaryOp(_3085_op, _2982_left, _2985_right, _2967_format);
              }
            }
          }
        }
      } else if (_source103.is_Or) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2964_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2964_op), _2982_left, _2985_right, _2967_format);
          } else {
            DAST._IBinOp _source120 = _2964_op;
            if (_source120.is_Eq) {
              bool _3086___mcc_h72 = _source120.dtor_referential;
              bool _3087___mcc_h73 = _source120.dtor_nullable;
              bool _3088_nullable = _3087___mcc_h73;
              bool _3089_referential = _3086___mcc_h72;
              {
                if (_3089_referential) {
                  if (_3088_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2982_left, _2985_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source120.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else if (_source120.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3090___mcc_h74 = _source120.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3091_op = _3090___mcc_h74;
              {
                r = RAST.Expr.create_BinaryOp(_3091_op, _2982_left, _2985_right, _2967_format);
              }
            }
          }
        }
      } else if (_source103.is_In) {
        {
          r = ((_2985_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_2982_left);
        }
      } else if (_source103.is_SeqProperPrefix) {
        r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2982_left, _2985_right, _2967_format);
      } else if (_source103.is_SeqPrefix) {
        r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _2982_left, _2985_right, _2967_format);
      } else if (_source103.is_SetMerge) {
        {
          r = ((_2982_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_2985_right);
        }
      } else if (_source103.is_SetSubtraction) {
        {
          r = ((_2982_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_2985_right);
        }
      } else if (_source103.is_SetIntersection) {
        {
          r = ((_2982_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_2985_right);
        }
      } else if (_source103.is_Subset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _2982_left, _2985_right, _2967_format);
        }
      } else if (_source103.is_ProperSubset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2982_left, _2985_right, _2967_format);
        }
      } else if (_source103.is_SetDisjoint) {
        {
          r = ((_2982_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_2985_right);
        }
      } else if (_source103.is_MapMerge) {
        {
          r = ((_2982_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_2985_right);
        }
      } else if (_source103.is_MapSubtraction) {
        {
          r = ((_2982_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_2985_right);
        }
      } else if (_source103.is_MultisetMerge) {
        {
          r = ((_2982_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_2985_right);
        }
      } else if (_source103.is_MultisetSubtraction) {
        {
          r = ((_2982_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_2985_right);
        }
      } else if (_source103.is_MultisetIntersection) {
        {
          r = ((_2982_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_2985_right);
        }
      } else if (_source103.is_Submultiset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _2982_left, _2985_right, _2967_format);
        }
      } else if (_source103.is_ProperSubmultiset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2982_left, _2985_right, _2967_format);
        }
      } else if (_source103.is_MultisetDisjoint) {
        {
          r = ((_2982_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_2985_right);
        }
      } else if (_source103.is_Concat) {
        {
          r = ((_2982_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_2985_right);
        }
      } else {
        Dafny.ISequence<Dafny.Rune> _3092___mcc_h22 = _source103.dtor_Passthrough_i_a0;
        {
          if ((DCOMP.COMP.OpTable).Contains(_2964_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2964_op), _2982_left, _2985_right, _2967_format);
          } else {
            DAST._IBinOp _source121 = _2964_op;
            if (_source121.is_Eq) {
              bool _3093___mcc_h75 = _source121.dtor_referential;
              bool _3094___mcc_h76 = _source121.dtor_nullable;
              bool _3095_nullable = _3094___mcc_h76;
              bool _3096_referential = _3093___mcc_h75;
              {
                if (_3096_referential) {
                  if (_3095_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2982_left, _2985_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source121.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else if (_source121.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2982_left, _2985_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3097___mcc_h77 = _source121.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3098_op = _3097___mcc_h77;
              {
                r = RAST.Expr.create_BinaryOp(_3098_op, _2982_left, _2985_right, _2967_format);
              }
            }
          }
        }
      }
      RAST._IExpr _out235;
      DCOMP._IOwnership _out236;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out235, out _out236);
      r = _out235;
      resultingOwnership = _out236;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2984_recIdentsL, _2987_recIdentsR);
      return ;
    }
    public void GenExprConvertFromNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs53 = e;
      DAST._IExpression _3099_expr = _let_tmp_rhs53.dtor_value;
      DAST._IType _3100_fromTpe = _let_tmp_rhs53.dtor_from;
      DAST._IType _3101_toTpe = _let_tmp_rhs53.dtor_typ;
      RAST._IExpr _3102_recursiveGen;
      DCOMP._IOwnership _3103_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3104_recIdents;
      RAST._IExpr _out237;
      DCOMP._IOwnership _out238;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out239;
      (this).GenExpr(_3099_expr, selfIdent, env, expectedOwnership, out _out237, out _out238, out _out239);
      _3102_recursiveGen = _out237;
      _3103_recOwned = _out238;
      _3104_recIdents = _out239;
      r = _3102_recursiveGen;
      if (object.Equals(_3103_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      RAST._IExpr _out240;
      DCOMP._IOwnership _out241;
      DCOMP.COMP.FromOwnership(r, _3103_recOwned, expectedOwnership, out _out240, out _out241);
      r = _out240;
      resultingOwnership = _out241;
      readIdents = _3104_recIdents;
    }
    public void GenExprConvertToNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IExpression _3105_expr = _let_tmp_rhs54.dtor_value;
      DAST._IType _3106_fromTpe = _let_tmp_rhs54.dtor_from;
      DAST._IType _3107_toTpe = _let_tmp_rhs54.dtor_typ;
      RAST._IExpr _3108_recursiveGen;
      DCOMP._IOwnership _3109_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3110_recIdents;
      RAST._IExpr _out242;
      DCOMP._IOwnership _out243;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out244;
      (this).GenExpr(_3105_expr, selfIdent, env, expectedOwnership, out _out242, out _out243, out _out244);
      _3108_recursiveGen = _out242;
      _3109_recOwned = _out243;
      _3110_recIdents = _out244;
      r = _3108_recursiveGen;
      if (object.Equals(_3109_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
      RAST._IExpr _out245;
      DCOMP._IOwnership _out246;
      DCOMP.COMP.FromOwnership(r, _3109_recOwned, expectedOwnership, out _out245, out _out246);
      r = _out245;
      resultingOwnership = _out246;
      readIdents = _3110_recIdents;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _3111_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _3112_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _3113_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _3113_toTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3114___v80 = _let_tmp_rhs56.dtor_Path_i_a0;
      Dafny.ISequence<DAST._IType> _3115___v81 = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      DAST._IType _3116_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _3117_range = _let_tmp_rhs57.dtor_range;
      bool _3118_erase = _let_tmp_rhs57.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _3119_attributes = _let_tmp_rhs57.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _3120_nativeToType;
      _3120_nativeToType = DCOMP.COMP.NewtypeToRustType(_3116_b, _3117_range);
      if (object.Equals(_3112_fromTpe, _3116_b)) {
        RAST._IExpr _3121_recursiveGen;
        DCOMP._IOwnership _3122_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3123_recIdents;
        RAST._IExpr _out247;
        DCOMP._IOwnership _out248;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out249;
        (this).GenExpr(_3111_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out247, out _out248, out _out249);
        _3121_recursiveGen = _out247;
        _3122_recOwned = _out248;
        _3123_recIdents = _out249;
        readIdents = _3123_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source122 = _3120_nativeToType;
        if (_source122.is_None) {
          if (_3118_erase) {
            r = _3121_recursiveGen;
          } else {
            RAST._IType _3124_rhsType;
            RAST._IType _out250;
            _out250 = (this).GenType(_3113_toTpe, true, false);
            _3124_rhsType = _out250;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_3124_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_3121_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out251;
          DCOMP._IOwnership _out252;
          DCOMP.COMP.FromOwnership(r, _3122_recOwned, expectedOwnership, out _out251, out _out252);
          r = _out251;
          resultingOwnership = _out252;
        } else {
          RAST._IType _3125___mcc_h0 = _source122.dtor_value;
          RAST._IType _3126_v = _3125___mcc_h0;
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3121_recursiveGen, RAST.Expr.create_ExprFromType(_3126_v)));
          RAST._IExpr _out253;
          DCOMP._IOwnership _out254;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out253, out _out254);
          r = _out253;
          resultingOwnership = _out254;
        }
      } else {
        if ((_3120_nativeToType).is_Some) {
          DAST._IType _source123 = _3112_fromTpe;
          if (_source123.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3127___mcc_h1 = _source123.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3128___mcc_h2 = _source123.dtor_typeArgs;
            DAST._IResolvedType _3129___mcc_h3 = _source123.dtor_resolved;
            DAST._IResolvedType _source124 = _3129___mcc_h3;
            if (_source124.is_Datatype) {
              DAST._IDatatypeType _3130___mcc_h7 = _source124.dtor_datatypeType;
            } else if (_source124.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3131___mcc_h9 = _source124.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3132___mcc_h10 = _source124.dtor_attributes;
            } else {
              DAST._IType _3133___mcc_h13 = _source124.dtor_baseType;
              DAST._INewtypeRange _3134___mcc_h14 = _source124.dtor_range;
              bool _3135___mcc_h15 = _source124.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3136___mcc_h16 = _source124.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3137_attributes0 = _3136___mcc_h16;
              bool _3138_erase0 = _3135___mcc_h15;
              DAST._INewtypeRange _3139_range0 = _3134___mcc_h14;
              DAST._IType _3140_b0 = _3133___mcc_h13;
              {
                Std.Wrappers._IOption<RAST._IType> _3141_nativeFromType;
                _3141_nativeFromType = DCOMP.COMP.NewtypeToRustType(_3140_b0, _3139_range0);
                if ((_3141_nativeFromType).is_Some) {
                  RAST._IExpr _3142_recursiveGen;
                  DCOMP._IOwnership _3143_recOwned;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3144_recIdents;
                  RAST._IExpr _out255;
                  DCOMP._IOwnership _out256;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out257;
                  (this).GenExpr(_3111_expr, selfIdent, env, expectedOwnership, out _out255, out _out256, out _out257);
                  _3142_recursiveGen = _out255;
                  _3143_recOwned = _out256;
                  _3144_recIdents = _out257;
                  RAST._IExpr _out258;
                  DCOMP._IOwnership _out259;
                  DCOMP.COMP.FromOwnership(RAST.Expr.create_TypeAscription(_3142_recursiveGen, (_3120_nativeToType).dtor_value), _3143_recOwned, expectedOwnership, out _out258, out _out259);
                  r = _out258;
                  resultingOwnership = _out259;
                  readIdents = _3144_recIdents;
                  return ;
                }
              }
            }
          } else if (_source123.is_Nullable) {
            DAST._IType _3145___mcc_h21 = _source123.dtor_Nullable_i_a0;
          } else if (_source123.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3146___mcc_h23 = _source123.dtor_Tuple_i_a0;
          } else if (_source123.is_Array) {
            DAST._IType _3147___mcc_h25 = _source123.dtor_element;
            BigInteger _3148___mcc_h26 = _source123.dtor_dims;
          } else if (_source123.is_Seq) {
            DAST._IType _3149___mcc_h29 = _source123.dtor_element;
          } else if (_source123.is_Set) {
            DAST._IType _3150___mcc_h31 = _source123.dtor_element;
          } else if (_source123.is_Multiset) {
            DAST._IType _3151___mcc_h33 = _source123.dtor_element;
          } else if (_source123.is_Map) {
            DAST._IType _3152___mcc_h35 = _source123.dtor_key;
            DAST._IType _3153___mcc_h36 = _source123.dtor_value;
          } else if (_source123.is_SetBuilder) {
            DAST._IType _3154___mcc_h39 = _source123.dtor_element;
          } else if (_source123.is_MapBuilder) {
            DAST._IType _3155___mcc_h41 = _source123.dtor_key;
            DAST._IType _3156___mcc_h42 = _source123.dtor_value;
          } else if (_source123.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3157___mcc_h45 = _source123.dtor_args;
            DAST._IType _3158___mcc_h46 = _source123.dtor_result;
          } else if (_source123.is_Primitive) {
            DAST._IPrimitive _3159___mcc_h49 = _source123.dtor_Primitive_i_a0;
          } else if (_source123.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3160___mcc_h51 = _source123.dtor_Passthrough_i_a0;
          } else {
            Dafny.ISequence<Dafny.Rune> _3161___mcc_h53 = _source123.dtor_TypeArg_i_a0;
          }
          if (object.Equals(_3112_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _3162_recursiveGen;
            DCOMP._IOwnership _3163_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3164_recIdents;
            RAST._IExpr _out260;
            DCOMP._IOwnership _out261;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out262;
            (this).GenExpr(_3111_expr, selfIdent, env, expectedOwnership, out _out260, out _out261, out _out262);
            _3162_recursiveGen = _out260;
            _3163_recOwned = _out261;
            _3164_recIdents = _out262;
            RAST._IExpr _out263;
            DCOMP._IOwnership _out264;
            DCOMP.COMP.FromOwnership(RAST.Expr.create_TypeAscription((_3162_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_3120_nativeToType).dtor_value), _3163_recOwned, expectedOwnership, out _out263, out _out264);
            r = _out263;
            resultingOwnership = _out264;
            readIdents = _3164_recIdents;
            return ;
          }
        }
        RAST._IExpr _out265;
        DCOMP._IOwnership _out266;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out267;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_3111_expr, _3112_fromTpe, _3116_b), _3116_b, _3113_toTpe), selfIdent, env, expectedOwnership, out _out265, out _out266, out _out267);
        r = _out265;
        resultingOwnership = _out266;
        readIdents = _out267;
      }
    }
    public void GenExprConvertFromNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs58 = e;
      DAST._IExpression _3165_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _3166_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _3167_toTpe = _let_tmp_rhs58.dtor_typ;
      DAST._IType _let_tmp_rhs59 = _3166_fromTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3168___v85 = _let_tmp_rhs59.dtor_Path_i_a0;
      Dafny.ISequence<DAST._IType> _3169___v86 = _let_tmp_rhs59.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs60 = _let_tmp_rhs59.dtor_resolved;
      DAST._IType _3170_b = _let_tmp_rhs60.dtor_baseType;
      DAST._INewtypeRange _3171_range = _let_tmp_rhs60.dtor_range;
      bool _3172_erase = _let_tmp_rhs60.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _3173_attributes = _let_tmp_rhs60.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _3174_nativeFromType;
      _3174_nativeFromType = DCOMP.COMP.NewtypeToRustType(_3170_b, _3171_range);
      if (object.Equals(_3170_b, _3167_toTpe)) {
        RAST._IExpr _3175_recursiveGen;
        DCOMP._IOwnership _3176_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3177_recIdents;
        RAST._IExpr _out268;
        DCOMP._IOwnership _out269;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out270;
        (this).GenExpr(_3165_expr, selfIdent, env, expectedOwnership, out _out268, out _out269, out _out270);
        _3175_recursiveGen = _out268;
        _3176_recOwned = _out269;
        _3177_recIdents = _out270;
        readIdents = _3177_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source125 = _3174_nativeFromType;
        if (_source125.is_None) {
          if (_3172_erase) {
            r = _3175_recursiveGen;
          } else {
            r = (_3175_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out271;
          DCOMP._IOwnership _out272;
          DCOMP.COMP.FromOwnership(r, _3176_recOwned, expectedOwnership, out _out271, out _out272);
          r = _out271;
          resultingOwnership = _out272;
        } else {
          RAST._IType _3178___mcc_h0 = _source125.dtor_value;
          RAST._IType _3179_v = _3178___mcc_h0;
          RAST._IType _3180_toTpeRust;
          RAST._IType _out273;
          _out273 = (this).GenType(_3167_toTpe, false, false);
          _3180_toTpeRust = _out273;
          r = (((_3175_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_3180_toTpeRust))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out274;
          DCOMP._IOwnership _out275;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out274, out _out275);
          r = _out274;
          resultingOwnership = _out275;
        }
      } else {
        if ((_3174_nativeFromType).is_Some) {
          if (object.Equals(_3167_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _3181_recursiveGen;
            DCOMP._IOwnership _3182_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3183_recIdents;
            RAST._IExpr _out276;
            DCOMP._IOwnership _out277;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out278;
            (this).GenExpr(_3165_expr, selfIdent, env, expectedOwnership, out _out276, out _out277, out _out278);
            _3181_recursiveGen = _out276;
            _3182_recOwned = _out277;
            _3183_recIdents = _out278;
            RAST._IExpr _out279;
            DCOMP._IOwnership _out280;
            DCOMP.COMP.FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_3181_recursiveGen, (this).DafnyCharUnderlying)), _3182_recOwned, expectedOwnership, out _out279, out _out280);
            r = _out279;
            resultingOwnership = _out280;
            readIdents = _3183_recIdents;
            return ;
          }
        }
        RAST._IExpr _out281;
        DCOMP._IOwnership _out282;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out283;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_3165_expr, _3166_fromTpe, _3170_b), _3170_b, _3167_toTpe), selfIdent, env, expectedOwnership, out _out281, out _out282, out _out283);
        r = _out281;
        resultingOwnership = _out282;
        readIdents = _out283;
      }
    }
    public void GenExprConvertNotImplemented(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs61 = e;
      DAST._IExpression _3184_expr = _let_tmp_rhs61.dtor_value;
      DAST._IType _3185_fromTpe = _let_tmp_rhs61.dtor_from;
      DAST._IType _3186_toTpe = _let_tmp_rhs61.dtor_typ;
      RAST._IType _3187_fromTpeGen;
      RAST._IType _out284;
      _out284 = (this).GenType(_3185_fromTpe, true, false);
      _3187_fromTpeGen = _out284;
      RAST._IType _3188_toTpeGen;
      RAST._IType _out285;
      _out285 = (this).GenType(_3186_toTpe, true, false);
      _3188_toTpeGen = _out285;
      RAST._IExpr _3189_recursiveGen;
      DCOMP._IOwnership _3190_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3191_recIdents;
      RAST._IExpr _out286;
      DCOMP._IOwnership _out287;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out288;
      (this).GenExpr(_3184_expr, selfIdent, env, expectedOwnership, out _out286, out _out287, out _out288);
      _3189_recursiveGen = _out286;
      _3190_recOwned = _out287;
      _3191_recIdents = _out288;
      Dafny.ISequence<Dafny.Rune> _3192_msg;
      _3192_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_3187_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_3188_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_3192_msg);
      r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_3189_recursiveGen)._ToString(DCOMP.__default.IND), _3192_msg));
      RAST._IExpr _out289;
      DCOMP._IOwnership _out290;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out289, out _out290);
      r = _out289;
      resultingOwnership = _out290;
      readIdents = _3191_recIdents;
    }
    public void GenExprConvert(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs62 = e;
      DAST._IExpression _3193_expr = _let_tmp_rhs62.dtor_value;
      DAST._IType _3194_fromTpe = _let_tmp_rhs62.dtor_from;
      DAST._IType _3195_toTpe = _let_tmp_rhs62.dtor_typ;
      if (object.Equals(_3194_fromTpe, _3195_toTpe)) {
        RAST._IExpr _3196_recursiveGen;
        DCOMP._IOwnership _3197_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3198_recIdents;
        RAST._IExpr _out291;
        DCOMP._IOwnership _out292;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out293;
        (this).GenExpr(_3193_expr, selfIdent, env, expectedOwnership, out _out291, out _out292, out _out293);
        _3196_recursiveGen = _out291;
        _3197_recOwned = _out292;
        _3198_recIdents = _out293;
        r = _3196_recursiveGen;
        RAST._IExpr _out294;
        DCOMP._IOwnership _out295;
        DCOMP.COMP.FromOwnership(r, _3197_recOwned, expectedOwnership, out _out294, out _out295);
        r = _out294;
        resultingOwnership = _out295;
        readIdents = _3198_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source126 = _System.Tuple2<DAST._IType, DAST._IType>.create(_3194_fromTpe, _3195_toTpe);
        DAST._IType _3199___mcc_h0 = _source126.dtor__0;
        DAST._IType _3200___mcc_h1 = _source126.dtor__1;
        DAST._IType _source127 = _3199___mcc_h0;
        if (_source127.is_Path) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3201___mcc_h4 = _source127.dtor_Path_i_a0;
          Dafny.ISequence<DAST._IType> _3202___mcc_h5 = _source127.dtor_typeArgs;
          DAST._IResolvedType _3203___mcc_h6 = _source127.dtor_resolved;
          DAST._IResolvedType _source128 = _3203___mcc_h6;
          if (_source128.is_Datatype) {
            DAST._IDatatypeType _3204___mcc_h16 = _source128.dtor_datatypeType;
            DAST._IType _source129 = _3200___mcc_h1;
            if (_source129.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3205___mcc_h20 = _source129.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3206___mcc_h21 = _source129.dtor_typeArgs;
              DAST._IResolvedType _3207___mcc_h22 = _source129.dtor_resolved;
              DAST._IResolvedType _source130 = _3207___mcc_h22;
              if (_source130.is_Datatype) {
                DAST._IDatatypeType _3208___mcc_h26 = _source130.dtor_datatypeType;
                {
                  RAST._IExpr _out296;
                  DCOMP._IOwnership _out297;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out298;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out296, out _out297, out _out298);
                  r = _out296;
                  resultingOwnership = _out297;
                  readIdents = _out298;
                }
              } else if (_source130.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3209___mcc_h28 = _source130.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3210___mcc_h29 = _source130.dtor_attributes;
                {
                  RAST._IExpr _out299;
                  DCOMP._IOwnership _out300;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out301;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out299, out _out300, out _out301);
                  r = _out299;
                  resultingOwnership = _out300;
                  readIdents = _out301;
                }
              } else {
                DAST._IType _3211___mcc_h32 = _source130.dtor_baseType;
                DAST._INewtypeRange _3212___mcc_h33 = _source130.dtor_range;
                bool _3213___mcc_h34 = _source130.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3214___mcc_h35 = _source130.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3215_attributes = _3214___mcc_h35;
                bool _3216_erase = _3213___mcc_h34;
                DAST._INewtypeRange _3217_range = _3212___mcc_h33;
                DAST._IType _3218_b = _3211___mcc_h32;
                {
                  RAST._IExpr _out302;
                  DCOMP._IOwnership _out303;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out304;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out302, out _out303, out _out304);
                  r = _out302;
                  resultingOwnership = _out303;
                  readIdents = _out304;
                }
              }
            } else if (_source129.is_Nullable) {
              DAST._IType _3219___mcc_h40 = _source129.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out305;
                DCOMP._IOwnership _out306;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out307;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out305, out _out306, out _out307);
                r = _out305;
                resultingOwnership = _out306;
                readIdents = _out307;
              }
            } else if (_source129.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3220___mcc_h42 = _source129.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out308;
                DCOMP._IOwnership _out309;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out310;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out308, out _out309, out _out310);
                r = _out308;
                resultingOwnership = _out309;
                readIdents = _out310;
              }
            } else if (_source129.is_Array) {
              DAST._IType _3221___mcc_h44 = _source129.dtor_element;
              BigInteger _3222___mcc_h45 = _source129.dtor_dims;
              {
                RAST._IExpr _out311;
                DCOMP._IOwnership _out312;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out313;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out311, out _out312, out _out313);
                r = _out311;
                resultingOwnership = _out312;
                readIdents = _out313;
              }
            } else if (_source129.is_Seq) {
              DAST._IType _3223___mcc_h48 = _source129.dtor_element;
              {
                RAST._IExpr _out314;
                DCOMP._IOwnership _out315;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out316;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out314, out _out315, out _out316);
                r = _out314;
                resultingOwnership = _out315;
                readIdents = _out316;
              }
            } else if (_source129.is_Set) {
              DAST._IType _3224___mcc_h50 = _source129.dtor_element;
              {
                RAST._IExpr _out317;
                DCOMP._IOwnership _out318;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out319;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out317, out _out318, out _out319);
                r = _out317;
                resultingOwnership = _out318;
                readIdents = _out319;
              }
            } else if (_source129.is_Multiset) {
              DAST._IType _3225___mcc_h52 = _source129.dtor_element;
              {
                RAST._IExpr _out320;
                DCOMP._IOwnership _out321;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out322;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out320, out _out321, out _out322);
                r = _out320;
                resultingOwnership = _out321;
                readIdents = _out322;
              }
            } else if (_source129.is_Map) {
              DAST._IType _3226___mcc_h54 = _source129.dtor_key;
              DAST._IType _3227___mcc_h55 = _source129.dtor_value;
              {
                RAST._IExpr _out323;
                DCOMP._IOwnership _out324;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out325;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out323, out _out324, out _out325);
                r = _out323;
                resultingOwnership = _out324;
                readIdents = _out325;
              }
            } else if (_source129.is_SetBuilder) {
              DAST._IType _3228___mcc_h58 = _source129.dtor_element;
              {
                RAST._IExpr _out326;
                DCOMP._IOwnership _out327;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out328;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out326, out _out327, out _out328);
                r = _out326;
                resultingOwnership = _out327;
                readIdents = _out328;
              }
            } else if (_source129.is_MapBuilder) {
              DAST._IType _3229___mcc_h60 = _source129.dtor_key;
              DAST._IType _3230___mcc_h61 = _source129.dtor_value;
              {
                RAST._IExpr _out329;
                DCOMP._IOwnership _out330;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out329, out _out330, out _out331);
                r = _out329;
                resultingOwnership = _out330;
                readIdents = _out331;
              }
            } else if (_source129.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3231___mcc_h64 = _source129.dtor_args;
              DAST._IType _3232___mcc_h65 = _source129.dtor_result;
              {
                RAST._IExpr _out332;
                DCOMP._IOwnership _out333;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out334;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out332, out _out333, out _out334);
                r = _out332;
                resultingOwnership = _out333;
                readIdents = _out334;
              }
            } else if (_source129.is_Primitive) {
              DAST._IPrimitive _3233___mcc_h68 = _source129.dtor_Primitive_i_a0;
              {
                RAST._IExpr _out335;
                DCOMP._IOwnership _out336;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out337;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out335, out _out336, out _out337);
                r = _out335;
                resultingOwnership = _out336;
                readIdents = _out337;
              }
            } else if (_source129.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3234___mcc_h70 = _source129.dtor_Passthrough_i_a0;
              {
                RAST._IExpr _out338;
                DCOMP._IOwnership _out339;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out340;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out338, out _out339, out _out340);
                r = _out338;
                resultingOwnership = _out339;
                readIdents = _out340;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3235___mcc_h72 = _source129.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out341;
                DCOMP._IOwnership _out342;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out343;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out341, out _out342, out _out343);
                r = _out341;
                resultingOwnership = _out342;
                readIdents = _out343;
              }
            }
          } else if (_source128.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3236___mcc_h74 = _source128.dtor_path;
            Dafny.ISequence<DAST._IAttribute> _3237___mcc_h75 = _source128.dtor_attributes;
            DAST._IType _source131 = _3200___mcc_h1;
            if (_source131.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3238___mcc_h82 = _source131.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3239___mcc_h83 = _source131.dtor_typeArgs;
              DAST._IResolvedType _3240___mcc_h84 = _source131.dtor_resolved;
              DAST._IResolvedType _source132 = _3240___mcc_h84;
              if (_source132.is_Datatype) {
                DAST._IDatatypeType _3241___mcc_h88 = _source132.dtor_datatypeType;
                {
                  RAST._IExpr _out344;
                  DCOMP._IOwnership _out345;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out346;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out344, out _out345, out _out346);
                  r = _out344;
                  resultingOwnership = _out345;
                  readIdents = _out346;
                }
              } else if (_source132.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3242___mcc_h90 = _source132.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3243___mcc_h91 = _source132.dtor_attributes;
                {
                  RAST._IExpr _out347;
                  DCOMP._IOwnership _out348;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out349;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out347, out _out348, out _out349);
                  r = _out347;
                  resultingOwnership = _out348;
                  readIdents = _out349;
                }
              } else {
                DAST._IType _3244___mcc_h94 = _source132.dtor_baseType;
                DAST._INewtypeRange _3245___mcc_h95 = _source132.dtor_range;
                bool _3246___mcc_h96 = _source132.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3247___mcc_h97 = _source132.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3248_attributes = _3247___mcc_h97;
                bool _3249_erase = _3246___mcc_h96;
                DAST._INewtypeRange _3250_range = _3245___mcc_h95;
                DAST._IType _3251_b = _3244___mcc_h94;
                {
                  RAST._IExpr _out350;
                  DCOMP._IOwnership _out351;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out352;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out350, out _out351, out _out352);
                  r = _out350;
                  resultingOwnership = _out351;
                  readIdents = _out352;
                }
              }
            } else if (_source131.is_Nullable) {
              DAST._IType _3252___mcc_h102 = _source131.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out353;
                DCOMP._IOwnership _out354;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out355;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out353, out _out354, out _out355);
                r = _out353;
                resultingOwnership = _out354;
                readIdents = _out355;
              }
            } else if (_source131.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3253___mcc_h104 = _source131.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out356;
                DCOMP._IOwnership _out357;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out358;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out356, out _out357, out _out358);
                r = _out356;
                resultingOwnership = _out357;
                readIdents = _out358;
              }
            } else if (_source131.is_Array) {
              DAST._IType _3254___mcc_h106 = _source131.dtor_element;
              BigInteger _3255___mcc_h107 = _source131.dtor_dims;
              {
                RAST._IExpr _out359;
                DCOMP._IOwnership _out360;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out361;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out359, out _out360, out _out361);
                r = _out359;
                resultingOwnership = _out360;
                readIdents = _out361;
              }
            } else if (_source131.is_Seq) {
              DAST._IType _3256___mcc_h110 = _source131.dtor_element;
              {
                RAST._IExpr _out362;
                DCOMP._IOwnership _out363;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out364;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out362, out _out363, out _out364);
                r = _out362;
                resultingOwnership = _out363;
                readIdents = _out364;
              }
            } else if (_source131.is_Set) {
              DAST._IType _3257___mcc_h112 = _source131.dtor_element;
              {
                RAST._IExpr _out365;
                DCOMP._IOwnership _out366;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out367;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out365, out _out366, out _out367);
                r = _out365;
                resultingOwnership = _out366;
                readIdents = _out367;
              }
            } else if (_source131.is_Multiset) {
              DAST._IType _3258___mcc_h114 = _source131.dtor_element;
              {
                RAST._IExpr _out368;
                DCOMP._IOwnership _out369;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out370;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out368, out _out369, out _out370);
                r = _out368;
                resultingOwnership = _out369;
                readIdents = _out370;
              }
            } else if (_source131.is_Map) {
              DAST._IType _3259___mcc_h116 = _source131.dtor_key;
              DAST._IType _3260___mcc_h117 = _source131.dtor_value;
              {
                RAST._IExpr _out371;
                DCOMP._IOwnership _out372;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out373;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out371, out _out372, out _out373);
                r = _out371;
                resultingOwnership = _out372;
                readIdents = _out373;
              }
            } else if (_source131.is_SetBuilder) {
              DAST._IType _3261___mcc_h120 = _source131.dtor_element;
              {
                RAST._IExpr _out374;
                DCOMP._IOwnership _out375;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out376;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out374, out _out375, out _out376);
                r = _out374;
                resultingOwnership = _out375;
                readIdents = _out376;
              }
            } else if (_source131.is_MapBuilder) {
              DAST._IType _3262___mcc_h122 = _source131.dtor_key;
              DAST._IType _3263___mcc_h123 = _source131.dtor_value;
              {
                RAST._IExpr _out377;
                DCOMP._IOwnership _out378;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out379;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out377, out _out378, out _out379);
                r = _out377;
                resultingOwnership = _out378;
                readIdents = _out379;
              }
            } else if (_source131.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3264___mcc_h126 = _source131.dtor_args;
              DAST._IType _3265___mcc_h127 = _source131.dtor_result;
              {
                RAST._IExpr _out380;
                DCOMP._IOwnership _out381;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out382;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out380, out _out381, out _out382);
                r = _out380;
                resultingOwnership = _out381;
                readIdents = _out382;
              }
            } else if (_source131.is_Primitive) {
              DAST._IPrimitive _3266___mcc_h130 = _source131.dtor_Primitive_i_a0;
              {
                RAST._IExpr _out383;
                DCOMP._IOwnership _out384;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out385;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out383, out _out384, out _out385);
                r = _out383;
                resultingOwnership = _out384;
                readIdents = _out385;
              }
            } else if (_source131.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3267___mcc_h132 = _source131.dtor_Passthrough_i_a0;
              {
                RAST._IExpr _out386;
                DCOMP._IOwnership _out387;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out388;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out386, out _out387, out _out388);
                r = _out386;
                resultingOwnership = _out387;
                readIdents = _out388;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3268___mcc_h134 = _source131.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out389;
                DCOMP._IOwnership _out390;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out391;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out389, out _out390, out _out391);
                r = _out389;
                resultingOwnership = _out390;
                readIdents = _out391;
              }
            }
          } else {
            DAST._IType _3269___mcc_h136 = _source128.dtor_baseType;
            DAST._INewtypeRange _3270___mcc_h137 = _source128.dtor_range;
            bool _3271___mcc_h138 = _source128.dtor_erase;
            Dafny.ISequence<DAST._IAttribute> _3272___mcc_h139 = _source128.dtor_attributes;
            DAST._IType _source133 = _3200___mcc_h1;
            if (_source133.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3273___mcc_h152 = _source133.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3274___mcc_h153 = _source133.dtor_typeArgs;
              DAST._IResolvedType _3275___mcc_h154 = _source133.dtor_resolved;
              DAST._IResolvedType _source134 = _3275___mcc_h154;
              if (_source134.is_Datatype) {
                DAST._IDatatypeType _3276___mcc_h161 = _source134.dtor_datatypeType;
                Dafny.ISequence<DAST._IAttribute> _3277_attributes = _3272___mcc_h139;
                bool _3278_erase = _3271___mcc_h138;
                DAST._INewtypeRange _3279_range = _3270___mcc_h137;
                DAST._IType _3280_b = _3269___mcc_h136;
                {
                  RAST._IExpr _out392;
                  DCOMP._IOwnership _out393;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out394;
                  (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out392, out _out393, out _out394);
                  r = _out392;
                  resultingOwnership = _out393;
                  readIdents = _out394;
                }
              } else if (_source134.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3281___mcc_h164 = _source134.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3282___mcc_h165 = _source134.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3283_attributes = _3272___mcc_h139;
                bool _3284_erase = _3271___mcc_h138;
                DAST._INewtypeRange _3285_range = _3270___mcc_h137;
                DAST._IType _3286_b = _3269___mcc_h136;
                {
                  RAST._IExpr _out395;
                  DCOMP._IOwnership _out396;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out397;
                  (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out395, out _out396, out _out397);
                  r = _out395;
                  resultingOwnership = _out396;
                  readIdents = _out397;
                }
              } else {
                DAST._IType _3287___mcc_h170 = _source134.dtor_baseType;
                DAST._INewtypeRange _3288___mcc_h171 = _source134.dtor_range;
                bool _3289___mcc_h172 = _source134.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3290___mcc_h173 = _source134.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3291_attributes = _3290___mcc_h173;
                bool _3292_erase = _3289___mcc_h172;
                DAST._INewtypeRange _3293_range = _3288___mcc_h171;
                DAST._IType _3294_b = _3287___mcc_h170;
                {
                  RAST._IExpr _out398;
                  DCOMP._IOwnership _out399;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out400;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out398, out _out399, out _out400);
                  r = _out398;
                  resultingOwnership = _out399;
                  readIdents = _out400;
                }
              }
            } else if (_source133.is_Nullable) {
              DAST._IType _3295___mcc_h182 = _source133.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out401;
                DCOMP._IOwnership _out402;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out401, out _out402, out _out403);
                r = _out401;
                resultingOwnership = _out402;
                readIdents = _out403;
              }
            } else if (_source133.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3296___mcc_h185 = _source133.dtor_Tuple_i_a0;
              Dafny.ISequence<DAST._IAttribute> _3297_attributes = _3272___mcc_h139;
              bool _3298_erase = _3271___mcc_h138;
              DAST._INewtypeRange _3299_range = _3270___mcc_h137;
              DAST._IType _3300_b = _3269___mcc_h136;
              {
                RAST._IExpr _out404;
                DCOMP._IOwnership _out405;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out406;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out404, out _out405, out _out406);
                r = _out404;
                resultingOwnership = _out405;
                readIdents = _out406;
              }
            } else if (_source133.is_Array) {
              DAST._IType _3301___mcc_h188 = _source133.dtor_element;
              BigInteger _3302___mcc_h189 = _source133.dtor_dims;
              Dafny.ISequence<DAST._IAttribute> _3303_attributes = _3272___mcc_h139;
              bool _3304_erase = _3271___mcc_h138;
              DAST._INewtypeRange _3305_range = _3270___mcc_h137;
              DAST._IType _3306_b = _3269___mcc_h136;
              {
                RAST._IExpr _out407;
                DCOMP._IOwnership _out408;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out407, out _out408, out _out409);
                r = _out407;
                resultingOwnership = _out408;
                readIdents = _out409;
              }
            } else if (_source133.is_Seq) {
              DAST._IType _3307___mcc_h194 = _source133.dtor_element;
              Dafny.ISequence<DAST._IAttribute> _3308_attributes = _3272___mcc_h139;
              bool _3309_erase = _3271___mcc_h138;
              DAST._INewtypeRange _3310_range = _3270___mcc_h137;
              DAST._IType _3311_b = _3269___mcc_h136;
              {
                RAST._IExpr _out410;
                DCOMP._IOwnership _out411;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out412;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out410, out _out411, out _out412);
                r = _out410;
                resultingOwnership = _out411;
                readIdents = _out412;
              }
            } else if (_source133.is_Set) {
              DAST._IType _3312___mcc_h197 = _source133.dtor_element;
              Dafny.ISequence<DAST._IAttribute> _3313_attributes = _3272___mcc_h139;
              bool _3314_erase = _3271___mcc_h138;
              DAST._INewtypeRange _3315_range = _3270___mcc_h137;
              DAST._IType _3316_b = _3269___mcc_h136;
              {
                RAST._IExpr _out413;
                DCOMP._IOwnership _out414;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out415;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out413, out _out414, out _out415);
                r = _out413;
                resultingOwnership = _out414;
                readIdents = _out415;
              }
            } else if (_source133.is_Multiset) {
              DAST._IType _3317___mcc_h200 = _source133.dtor_element;
              Dafny.ISequence<DAST._IAttribute> _3318_attributes = _3272___mcc_h139;
              bool _3319_erase = _3271___mcc_h138;
              DAST._INewtypeRange _3320_range = _3270___mcc_h137;
              DAST._IType _3321_b = _3269___mcc_h136;
              {
                RAST._IExpr _out416;
                DCOMP._IOwnership _out417;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out418;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out416, out _out417, out _out418);
                r = _out416;
                resultingOwnership = _out417;
                readIdents = _out418;
              }
            } else if (_source133.is_Map) {
              DAST._IType _3322___mcc_h203 = _source133.dtor_key;
              DAST._IType _3323___mcc_h204 = _source133.dtor_value;
              Dafny.ISequence<DAST._IAttribute> _3324_attributes = _3272___mcc_h139;
              bool _3325_erase = _3271___mcc_h138;
              DAST._INewtypeRange _3326_range = _3270___mcc_h137;
              DAST._IType _3327_b = _3269___mcc_h136;
              {
                RAST._IExpr _out419;
                DCOMP._IOwnership _out420;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out421;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out419, out _out420, out _out421);
                r = _out419;
                resultingOwnership = _out420;
                readIdents = _out421;
              }
            } else if (_source133.is_SetBuilder) {
              DAST._IType _3328___mcc_h209 = _source133.dtor_element;
              Dafny.ISequence<DAST._IAttribute> _3329_attributes = _3272___mcc_h139;
              bool _3330_erase = _3271___mcc_h138;
              DAST._INewtypeRange _3331_range = _3270___mcc_h137;
              DAST._IType _3332_b = _3269___mcc_h136;
              {
                RAST._IExpr _out422;
                DCOMP._IOwnership _out423;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out424;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out422, out _out423, out _out424);
                r = _out422;
                resultingOwnership = _out423;
                readIdents = _out424;
              }
            } else if (_source133.is_MapBuilder) {
              DAST._IType _3333___mcc_h212 = _source133.dtor_key;
              DAST._IType _3334___mcc_h213 = _source133.dtor_value;
              Dafny.ISequence<DAST._IAttribute> _3335_attributes = _3272___mcc_h139;
              bool _3336_erase = _3271___mcc_h138;
              DAST._INewtypeRange _3337_range = _3270___mcc_h137;
              DAST._IType _3338_b = _3269___mcc_h136;
              {
                RAST._IExpr _out425;
                DCOMP._IOwnership _out426;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out427;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out425, out _out426, out _out427);
                r = _out425;
                resultingOwnership = _out426;
                readIdents = _out427;
              }
            } else if (_source133.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3339___mcc_h218 = _source133.dtor_args;
              DAST._IType _3340___mcc_h219 = _source133.dtor_result;
              Dafny.ISequence<DAST._IAttribute> _3341_attributes = _3272___mcc_h139;
              bool _3342_erase = _3271___mcc_h138;
              DAST._INewtypeRange _3343_range = _3270___mcc_h137;
              DAST._IType _3344_b = _3269___mcc_h136;
              {
                RAST._IExpr _out428;
                DCOMP._IOwnership _out429;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out430;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out428, out _out429, out _out430);
                r = _out428;
                resultingOwnership = _out429;
                readIdents = _out430;
              }
            } else if (_source133.is_Primitive) {
              DAST._IPrimitive _3345___mcc_h224 = _source133.dtor_Primitive_i_a0;
              Dafny.ISequence<DAST._IAttribute> _3346_attributes = _3272___mcc_h139;
              bool _3347_erase = _3271___mcc_h138;
              DAST._INewtypeRange _3348_range = _3270___mcc_h137;
              DAST._IType _3349_b = _3269___mcc_h136;
              {
                RAST._IExpr _out431;
                DCOMP._IOwnership _out432;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out433;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out431, out _out432, out _out433);
                r = _out431;
                resultingOwnership = _out432;
                readIdents = _out433;
              }
            } else if (_source133.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3350___mcc_h227 = _source133.dtor_Passthrough_i_a0;
              Dafny.ISequence<DAST._IAttribute> _3351_attributes = _3272___mcc_h139;
              bool _3352_erase = _3271___mcc_h138;
              DAST._INewtypeRange _3353_range = _3270___mcc_h137;
              DAST._IType _3354_b = _3269___mcc_h136;
              {
                RAST._IExpr _out434;
                DCOMP._IOwnership _out435;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out436;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out434, out _out435, out _out436);
                r = _out434;
                resultingOwnership = _out435;
                readIdents = _out436;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3355___mcc_h230 = _source133.dtor_TypeArg_i_a0;
              Dafny.ISequence<DAST._IAttribute> _3356_attributes = _3272___mcc_h139;
              bool _3357_erase = _3271___mcc_h138;
              DAST._INewtypeRange _3358_range = _3270___mcc_h137;
              DAST._IType _3359_b = _3269___mcc_h136;
              {
                RAST._IExpr _out437;
                DCOMP._IOwnership _out438;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out439;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out437, out _out438, out _out439);
                r = _out437;
                resultingOwnership = _out438;
                readIdents = _out439;
              }
            }
          }
        } else if (_source127.is_Nullable) {
          DAST._IType _3360___mcc_h233 = _source127.dtor_Nullable_i_a0;
          DAST._IType _source135 = _3200___mcc_h1;
          if (_source135.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3361___mcc_h237 = _source135.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3362___mcc_h238 = _source135.dtor_typeArgs;
            DAST._IResolvedType _3363___mcc_h239 = _source135.dtor_resolved;
            DAST._IResolvedType _source136 = _3363___mcc_h239;
            if (_source136.is_Datatype) {
              DAST._IDatatypeType _3364___mcc_h246 = _source136.dtor_datatypeType;
              {
                RAST._IExpr _out440;
                DCOMP._IOwnership _out441;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out442;
                (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out440, out _out441, out _out442);
                r = _out440;
                resultingOwnership = _out441;
                readIdents = _out442;
              }
            } else if (_source136.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3365___mcc_h249 = _source136.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3366___mcc_h250 = _source136.dtor_attributes;
              {
                RAST._IExpr _out443;
                DCOMP._IOwnership _out444;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out445;
                (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out443, out _out444, out _out445);
                r = _out443;
                resultingOwnership = _out444;
                readIdents = _out445;
              }
            } else {
              DAST._IType _3367___mcc_h255 = _source136.dtor_baseType;
              DAST._INewtypeRange _3368___mcc_h256 = _source136.dtor_range;
              bool _3369___mcc_h257 = _source136.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3370___mcc_h258 = _source136.dtor_attributes;
              {
                RAST._IExpr _out446;
                DCOMP._IOwnership _out447;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out448;
                (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out446, out _out447, out _out448);
                r = _out446;
                resultingOwnership = _out447;
                readIdents = _out448;
              }
            }
          } else if (_source135.is_Nullable) {
            DAST._IType _3371___mcc_h267 = _source135.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out449;
              DCOMP._IOwnership _out450;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out449, out _out450, out _out451);
              r = _out449;
              resultingOwnership = _out450;
              readIdents = _out451;
            }
          } else if (_source135.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3372___mcc_h270 = _source135.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out452;
              DCOMP._IOwnership _out453;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out454;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out452, out _out453, out _out454);
              r = _out452;
              resultingOwnership = _out453;
              readIdents = _out454;
            }
          } else if (_source135.is_Array) {
            DAST._IType _3373___mcc_h273 = _source135.dtor_element;
            BigInteger _3374___mcc_h274 = _source135.dtor_dims;
            {
              RAST._IExpr _out455;
              DCOMP._IOwnership _out456;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out457;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out455, out _out456, out _out457);
              r = _out455;
              resultingOwnership = _out456;
              readIdents = _out457;
            }
          } else if (_source135.is_Seq) {
            DAST._IType _3375___mcc_h279 = _source135.dtor_element;
            {
              RAST._IExpr _out458;
              DCOMP._IOwnership _out459;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out460;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out458, out _out459, out _out460);
              r = _out458;
              resultingOwnership = _out459;
              readIdents = _out460;
            }
          } else if (_source135.is_Set) {
            DAST._IType _3376___mcc_h282 = _source135.dtor_element;
            {
              RAST._IExpr _out461;
              DCOMP._IOwnership _out462;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out463;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out461, out _out462, out _out463);
              r = _out461;
              resultingOwnership = _out462;
              readIdents = _out463;
            }
          } else if (_source135.is_Multiset) {
            DAST._IType _3377___mcc_h285 = _source135.dtor_element;
            {
              RAST._IExpr _out464;
              DCOMP._IOwnership _out465;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out466;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out464, out _out465, out _out466);
              r = _out464;
              resultingOwnership = _out465;
              readIdents = _out466;
            }
          } else if (_source135.is_Map) {
            DAST._IType _3378___mcc_h288 = _source135.dtor_key;
            DAST._IType _3379___mcc_h289 = _source135.dtor_value;
            {
              RAST._IExpr _out467;
              DCOMP._IOwnership _out468;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out469;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out467, out _out468, out _out469);
              r = _out467;
              resultingOwnership = _out468;
              readIdents = _out469;
            }
          } else if (_source135.is_SetBuilder) {
            DAST._IType _3380___mcc_h294 = _source135.dtor_element;
            {
              RAST._IExpr _out470;
              DCOMP._IOwnership _out471;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out472;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out470, out _out471, out _out472);
              r = _out470;
              resultingOwnership = _out471;
              readIdents = _out472;
            }
          } else if (_source135.is_MapBuilder) {
            DAST._IType _3381___mcc_h297 = _source135.dtor_key;
            DAST._IType _3382___mcc_h298 = _source135.dtor_value;
            {
              RAST._IExpr _out473;
              DCOMP._IOwnership _out474;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out475;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out473, out _out474, out _out475);
              r = _out473;
              resultingOwnership = _out474;
              readIdents = _out475;
            }
          } else if (_source135.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3383___mcc_h303 = _source135.dtor_args;
            DAST._IType _3384___mcc_h304 = _source135.dtor_result;
            {
              RAST._IExpr _out476;
              DCOMP._IOwnership _out477;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out478;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out476, out _out477, out _out478);
              r = _out476;
              resultingOwnership = _out477;
              readIdents = _out478;
            }
          } else if (_source135.is_Primitive) {
            DAST._IPrimitive _3385___mcc_h309 = _source135.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out479;
              DCOMP._IOwnership _out480;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out481;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out479, out _out480, out _out481);
              r = _out479;
              resultingOwnership = _out480;
              readIdents = _out481;
            }
          } else if (_source135.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3386___mcc_h312 = _source135.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out482;
              DCOMP._IOwnership _out483;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out484;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out482, out _out483, out _out484);
              r = _out482;
              resultingOwnership = _out483;
              readIdents = _out484;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3387___mcc_h315 = _source135.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out485;
              DCOMP._IOwnership _out486;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out487;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out485, out _out486, out _out487);
              r = _out485;
              resultingOwnership = _out486;
              readIdents = _out487;
            }
          }
        } else if (_source127.is_Tuple) {
          Dafny.ISequence<DAST._IType> _3388___mcc_h318 = _source127.dtor_Tuple_i_a0;
          DAST._IType _source137 = _3200___mcc_h1;
          if (_source137.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3389___mcc_h322 = _source137.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3390___mcc_h323 = _source137.dtor_typeArgs;
            DAST._IResolvedType _3391___mcc_h324 = _source137.dtor_resolved;
            DAST._IResolvedType _source138 = _3391___mcc_h324;
            if (_source138.is_Datatype) {
              DAST._IDatatypeType _3392___mcc_h328 = _source138.dtor_datatypeType;
              {
                RAST._IExpr _out488;
                DCOMP._IOwnership _out489;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out490;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out488, out _out489, out _out490);
                r = _out488;
                resultingOwnership = _out489;
                readIdents = _out490;
              }
            } else if (_source138.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3393___mcc_h330 = _source138.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3394___mcc_h331 = _source138.dtor_attributes;
              {
                RAST._IExpr _out491;
                DCOMP._IOwnership _out492;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out493;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out491, out _out492, out _out493);
                r = _out491;
                resultingOwnership = _out492;
                readIdents = _out493;
              }
            } else {
              DAST._IType _3395___mcc_h334 = _source138.dtor_baseType;
              DAST._INewtypeRange _3396___mcc_h335 = _source138.dtor_range;
              bool _3397___mcc_h336 = _source138.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3398___mcc_h337 = _source138.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3399_attributes = _3398___mcc_h337;
              bool _3400_erase = _3397___mcc_h336;
              DAST._INewtypeRange _3401_range = _3396___mcc_h335;
              DAST._IType _3402_b = _3395___mcc_h334;
              {
                RAST._IExpr _out494;
                DCOMP._IOwnership _out495;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out496;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out494, out _out495, out _out496);
                r = _out494;
                resultingOwnership = _out495;
                readIdents = _out496;
              }
            }
          } else if (_source137.is_Nullable) {
            DAST._IType _3403___mcc_h342 = _source137.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out497;
              DCOMP._IOwnership _out498;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out499;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out497, out _out498, out _out499);
              r = _out497;
              resultingOwnership = _out498;
              readIdents = _out499;
            }
          } else if (_source137.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3404___mcc_h344 = _source137.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out500;
              DCOMP._IOwnership _out501;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out502;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out500, out _out501, out _out502);
              r = _out500;
              resultingOwnership = _out501;
              readIdents = _out502;
            }
          } else if (_source137.is_Array) {
            DAST._IType _3405___mcc_h346 = _source137.dtor_element;
            BigInteger _3406___mcc_h347 = _source137.dtor_dims;
            {
              RAST._IExpr _out503;
              DCOMP._IOwnership _out504;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out505;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out503, out _out504, out _out505);
              r = _out503;
              resultingOwnership = _out504;
              readIdents = _out505;
            }
          } else if (_source137.is_Seq) {
            DAST._IType _3407___mcc_h350 = _source137.dtor_element;
            {
              RAST._IExpr _out506;
              DCOMP._IOwnership _out507;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out508;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out506, out _out507, out _out508);
              r = _out506;
              resultingOwnership = _out507;
              readIdents = _out508;
            }
          } else if (_source137.is_Set) {
            DAST._IType _3408___mcc_h352 = _source137.dtor_element;
            {
              RAST._IExpr _out509;
              DCOMP._IOwnership _out510;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out511;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out509, out _out510, out _out511);
              r = _out509;
              resultingOwnership = _out510;
              readIdents = _out511;
            }
          } else if (_source137.is_Multiset) {
            DAST._IType _3409___mcc_h354 = _source137.dtor_element;
            {
              RAST._IExpr _out512;
              DCOMP._IOwnership _out513;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out514;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out512, out _out513, out _out514);
              r = _out512;
              resultingOwnership = _out513;
              readIdents = _out514;
            }
          } else if (_source137.is_Map) {
            DAST._IType _3410___mcc_h356 = _source137.dtor_key;
            DAST._IType _3411___mcc_h357 = _source137.dtor_value;
            {
              RAST._IExpr _out515;
              DCOMP._IOwnership _out516;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out517;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out515, out _out516, out _out517);
              r = _out515;
              resultingOwnership = _out516;
              readIdents = _out517;
            }
          } else if (_source137.is_SetBuilder) {
            DAST._IType _3412___mcc_h360 = _source137.dtor_element;
            {
              RAST._IExpr _out518;
              DCOMP._IOwnership _out519;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out520;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out518, out _out519, out _out520);
              r = _out518;
              resultingOwnership = _out519;
              readIdents = _out520;
            }
          } else if (_source137.is_MapBuilder) {
            DAST._IType _3413___mcc_h362 = _source137.dtor_key;
            DAST._IType _3414___mcc_h363 = _source137.dtor_value;
            {
              RAST._IExpr _out521;
              DCOMP._IOwnership _out522;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out523;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out521, out _out522, out _out523);
              r = _out521;
              resultingOwnership = _out522;
              readIdents = _out523;
            }
          } else if (_source137.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3415___mcc_h366 = _source137.dtor_args;
            DAST._IType _3416___mcc_h367 = _source137.dtor_result;
            {
              RAST._IExpr _out524;
              DCOMP._IOwnership _out525;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out526;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out524, out _out525, out _out526);
              r = _out524;
              resultingOwnership = _out525;
              readIdents = _out526;
            }
          } else if (_source137.is_Primitive) {
            DAST._IPrimitive _3417___mcc_h370 = _source137.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out527;
              DCOMP._IOwnership _out528;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out529;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out527, out _out528, out _out529);
              r = _out527;
              resultingOwnership = _out528;
              readIdents = _out529;
            }
          } else if (_source137.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3418___mcc_h372 = _source137.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out530;
              DCOMP._IOwnership _out531;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out532;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out530, out _out531, out _out532);
              r = _out530;
              resultingOwnership = _out531;
              readIdents = _out532;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3419___mcc_h374 = _source137.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out533;
              DCOMP._IOwnership _out534;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out535;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out533, out _out534, out _out535);
              r = _out533;
              resultingOwnership = _out534;
              readIdents = _out535;
            }
          }
        } else if (_source127.is_Array) {
          DAST._IType _3420___mcc_h376 = _source127.dtor_element;
          BigInteger _3421___mcc_h377 = _source127.dtor_dims;
          DAST._IType _source139 = _3200___mcc_h1;
          if (_source139.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3422___mcc_h384 = _source139.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3423___mcc_h385 = _source139.dtor_typeArgs;
            DAST._IResolvedType _3424___mcc_h386 = _source139.dtor_resolved;
            DAST._IResolvedType _source140 = _3424___mcc_h386;
            if (_source140.is_Datatype) {
              DAST._IDatatypeType _3425___mcc_h390 = _source140.dtor_datatypeType;
              {
                RAST._IExpr _out536;
                DCOMP._IOwnership _out537;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out538;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out536, out _out537, out _out538);
                r = _out536;
                resultingOwnership = _out537;
                readIdents = _out538;
              }
            } else if (_source140.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3426___mcc_h392 = _source140.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3427___mcc_h393 = _source140.dtor_attributes;
              {
                RAST._IExpr _out539;
                DCOMP._IOwnership _out540;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out539, out _out540, out _out541);
                r = _out539;
                resultingOwnership = _out540;
                readIdents = _out541;
              }
            } else {
              DAST._IType _3428___mcc_h396 = _source140.dtor_baseType;
              DAST._INewtypeRange _3429___mcc_h397 = _source140.dtor_range;
              bool _3430___mcc_h398 = _source140.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3431___mcc_h399 = _source140.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3432_attributes = _3431___mcc_h399;
              bool _3433_erase = _3430___mcc_h398;
              DAST._INewtypeRange _3434_range = _3429___mcc_h397;
              DAST._IType _3435_b = _3428___mcc_h396;
              {
                RAST._IExpr _out542;
                DCOMP._IOwnership _out543;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out544;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out542, out _out543, out _out544);
                r = _out542;
                resultingOwnership = _out543;
                readIdents = _out544;
              }
            }
          } else if (_source139.is_Nullable) {
            DAST._IType _3436___mcc_h404 = _source139.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out545;
              DCOMP._IOwnership _out546;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out547;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out545, out _out546, out _out547);
              r = _out545;
              resultingOwnership = _out546;
              readIdents = _out547;
            }
          } else if (_source139.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3437___mcc_h406 = _source139.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out548;
              DCOMP._IOwnership _out549;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out550;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out548, out _out549, out _out550);
              r = _out548;
              resultingOwnership = _out549;
              readIdents = _out550;
            }
          } else if (_source139.is_Array) {
            DAST._IType _3438___mcc_h408 = _source139.dtor_element;
            BigInteger _3439___mcc_h409 = _source139.dtor_dims;
            {
              RAST._IExpr _out551;
              DCOMP._IOwnership _out552;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out553;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out551, out _out552, out _out553);
              r = _out551;
              resultingOwnership = _out552;
              readIdents = _out553;
            }
          } else if (_source139.is_Seq) {
            DAST._IType _3440___mcc_h412 = _source139.dtor_element;
            {
              RAST._IExpr _out554;
              DCOMP._IOwnership _out555;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out556;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out554, out _out555, out _out556);
              r = _out554;
              resultingOwnership = _out555;
              readIdents = _out556;
            }
          } else if (_source139.is_Set) {
            DAST._IType _3441___mcc_h414 = _source139.dtor_element;
            {
              RAST._IExpr _out557;
              DCOMP._IOwnership _out558;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out559;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out557, out _out558, out _out559);
              r = _out557;
              resultingOwnership = _out558;
              readIdents = _out559;
            }
          } else if (_source139.is_Multiset) {
            DAST._IType _3442___mcc_h416 = _source139.dtor_element;
            {
              RAST._IExpr _out560;
              DCOMP._IOwnership _out561;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out562;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out560, out _out561, out _out562);
              r = _out560;
              resultingOwnership = _out561;
              readIdents = _out562;
            }
          } else if (_source139.is_Map) {
            DAST._IType _3443___mcc_h418 = _source139.dtor_key;
            DAST._IType _3444___mcc_h419 = _source139.dtor_value;
            {
              RAST._IExpr _out563;
              DCOMP._IOwnership _out564;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out565;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out563, out _out564, out _out565);
              r = _out563;
              resultingOwnership = _out564;
              readIdents = _out565;
            }
          } else if (_source139.is_SetBuilder) {
            DAST._IType _3445___mcc_h422 = _source139.dtor_element;
            {
              RAST._IExpr _out566;
              DCOMP._IOwnership _out567;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out568;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out566, out _out567, out _out568);
              r = _out566;
              resultingOwnership = _out567;
              readIdents = _out568;
            }
          } else if (_source139.is_MapBuilder) {
            DAST._IType _3446___mcc_h424 = _source139.dtor_key;
            DAST._IType _3447___mcc_h425 = _source139.dtor_value;
            {
              RAST._IExpr _out569;
              DCOMP._IOwnership _out570;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out571;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out569, out _out570, out _out571);
              r = _out569;
              resultingOwnership = _out570;
              readIdents = _out571;
            }
          } else if (_source139.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3448___mcc_h428 = _source139.dtor_args;
            DAST._IType _3449___mcc_h429 = _source139.dtor_result;
            {
              RAST._IExpr _out572;
              DCOMP._IOwnership _out573;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out574;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out572, out _out573, out _out574);
              r = _out572;
              resultingOwnership = _out573;
              readIdents = _out574;
            }
          } else if (_source139.is_Primitive) {
            DAST._IPrimitive _3450___mcc_h432 = _source139.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out575;
              DCOMP._IOwnership _out576;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out577;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out575, out _out576, out _out577);
              r = _out575;
              resultingOwnership = _out576;
              readIdents = _out577;
            }
          } else if (_source139.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3451___mcc_h434 = _source139.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out578;
              DCOMP._IOwnership _out579;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out580;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out578, out _out579, out _out580);
              r = _out578;
              resultingOwnership = _out579;
              readIdents = _out580;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3452___mcc_h436 = _source139.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out581;
              DCOMP._IOwnership _out582;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out583;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out581, out _out582, out _out583);
              r = _out581;
              resultingOwnership = _out582;
              readIdents = _out583;
            }
          }
        } else if (_source127.is_Seq) {
          DAST._IType _3453___mcc_h438 = _source127.dtor_element;
          DAST._IType _source141 = _3200___mcc_h1;
          if (_source141.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3454___mcc_h442 = _source141.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3455___mcc_h443 = _source141.dtor_typeArgs;
            DAST._IResolvedType _3456___mcc_h444 = _source141.dtor_resolved;
            DAST._IResolvedType _source142 = _3456___mcc_h444;
            if (_source142.is_Datatype) {
              DAST._IDatatypeType _3457___mcc_h448 = _source142.dtor_datatypeType;
              {
                RAST._IExpr _out584;
                DCOMP._IOwnership _out585;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out586;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out584, out _out585, out _out586);
                r = _out584;
                resultingOwnership = _out585;
                readIdents = _out586;
              }
            } else if (_source142.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3458___mcc_h450 = _source142.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3459___mcc_h451 = _source142.dtor_attributes;
              {
                RAST._IExpr _out587;
                DCOMP._IOwnership _out588;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out589;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out587, out _out588, out _out589);
                r = _out587;
                resultingOwnership = _out588;
                readIdents = _out589;
              }
            } else {
              DAST._IType _3460___mcc_h454 = _source142.dtor_baseType;
              DAST._INewtypeRange _3461___mcc_h455 = _source142.dtor_range;
              bool _3462___mcc_h456 = _source142.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3463___mcc_h457 = _source142.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3464_attributes = _3463___mcc_h457;
              bool _3465_erase = _3462___mcc_h456;
              DAST._INewtypeRange _3466_range = _3461___mcc_h455;
              DAST._IType _3467_b = _3460___mcc_h454;
              {
                RAST._IExpr _out590;
                DCOMP._IOwnership _out591;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out592;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out590, out _out591, out _out592);
                r = _out590;
                resultingOwnership = _out591;
                readIdents = _out592;
              }
            }
          } else if (_source141.is_Nullable) {
            DAST._IType _3468___mcc_h462 = _source141.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out593;
              DCOMP._IOwnership _out594;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out595;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out593, out _out594, out _out595);
              r = _out593;
              resultingOwnership = _out594;
              readIdents = _out595;
            }
          } else if (_source141.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3469___mcc_h464 = _source141.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out596;
              DCOMP._IOwnership _out597;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out598;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out596, out _out597, out _out598);
              r = _out596;
              resultingOwnership = _out597;
              readIdents = _out598;
            }
          } else if (_source141.is_Array) {
            DAST._IType _3470___mcc_h466 = _source141.dtor_element;
            BigInteger _3471___mcc_h467 = _source141.dtor_dims;
            {
              RAST._IExpr _out599;
              DCOMP._IOwnership _out600;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out601;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out599, out _out600, out _out601);
              r = _out599;
              resultingOwnership = _out600;
              readIdents = _out601;
            }
          } else if (_source141.is_Seq) {
            DAST._IType _3472___mcc_h470 = _source141.dtor_element;
            {
              RAST._IExpr _out602;
              DCOMP._IOwnership _out603;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out604;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out602, out _out603, out _out604);
              r = _out602;
              resultingOwnership = _out603;
              readIdents = _out604;
            }
          } else if (_source141.is_Set) {
            DAST._IType _3473___mcc_h472 = _source141.dtor_element;
            {
              RAST._IExpr _out605;
              DCOMP._IOwnership _out606;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out607;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out605, out _out606, out _out607);
              r = _out605;
              resultingOwnership = _out606;
              readIdents = _out607;
            }
          } else if (_source141.is_Multiset) {
            DAST._IType _3474___mcc_h474 = _source141.dtor_element;
            {
              RAST._IExpr _out608;
              DCOMP._IOwnership _out609;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out610;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out608, out _out609, out _out610);
              r = _out608;
              resultingOwnership = _out609;
              readIdents = _out610;
            }
          } else if (_source141.is_Map) {
            DAST._IType _3475___mcc_h476 = _source141.dtor_key;
            DAST._IType _3476___mcc_h477 = _source141.dtor_value;
            {
              RAST._IExpr _out611;
              DCOMP._IOwnership _out612;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out613;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out611, out _out612, out _out613);
              r = _out611;
              resultingOwnership = _out612;
              readIdents = _out613;
            }
          } else if (_source141.is_SetBuilder) {
            DAST._IType _3477___mcc_h480 = _source141.dtor_element;
            {
              RAST._IExpr _out614;
              DCOMP._IOwnership _out615;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out616;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out614, out _out615, out _out616);
              r = _out614;
              resultingOwnership = _out615;
              readIdents = _out616;
            }
          } else if (_source141.is_MapBuilder) {
            DAST._IType _3478___mcc_h482 = _source141.dtor_key;
            DAST._IType _3479___mcc_h483 = _source141.dtor_value;
            {
              RAST._IExpr _out617;
              DCOMP._IOwnership _out618;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out619;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out617, out _out618, out _out619);
              r = _out617;
              resultingOwnership = _out618;
              readIdents = _out619;
            }
          } else if (_source141.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3480___mcc_h486 = _source141.dtor_args;
            DAST._IType _3481___mcc_h487 = _source141.dtor_result;
            {
              RAST._IExpr _out620;
              DCOMP._IOwnership _out621;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out620, out _out621, out _out622);
              r = _out620;
              resultingOwnership = _out621;
              readIdents = _out622;
            }
          } else if (_source141.is_Primitive) {
            DAST._IPrimitive _3482___mcc_h490 = _source141.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out623;
              DCOMP._IOwnership _out624;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out625;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out623, out _out624, out _out625);
              r = _out623;
              resultingOwnership = _out624;
              readIdents = _out625;
            }
          } else if (_source141.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3483___mcc_h492 = _source141.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out626;
              DCOMP._IOwnership _out627;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out628;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out626, out _out627, out _out628);
              r = _out626;
              resultingOwnership = _out627;
              readIdents = _out628;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3484___mcc_h494 = _source141.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out629;
              DCOMP._IOwnership _out630;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out631;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out629, out _out630, out _out631);
              r = _out629;
              resultingOwnership = _out630;
              readIdents = _out631;
            }
          }
        } else if (_source127.is_Set) {
          DAST._IType _3485___mcc_h496 = _source127.dtor_element;
          DAST._IType _source143 = _3200___mcc_h1;
          if (_source143.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3486___mcc_h500 = _source143.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3487___mcc_h501 = _source143.dtor_typeArgs;
            DAST._IResolvedType _3488___mcc_h502 = _source143.dtor_resolved;
            DAST._IResolvedType _source144 = _3488___mcc_h502;
            if (_source144.is_Datatype) {
              DAST._IDatatypeType _3489___mcc_h506 = _source144.dtor_datatypeType;
              {
                RAST._IExpr _out632;
                DCOMP._IOwnership _out633;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out634;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out632, out _out633, out _out634);
                r = _out632;
                resultingOwnership = _out633;
                readIdents = _out634;
              }
            } else if (_source144.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3490___mcc_h508 = _source144.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3491___mcc_h509 = _source144.dtor_attributes;
              {
                RAST._IExpr _out635;
                DCOMP._IOwnership _out636;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out637;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out635, out _out636, out _out637);
                r = _out635;
                resultingOwnership = _out636;
                readIdents = _out637;
              }
            } else {
              DAST._IType _3492___mcc_h512 = _source144.dtor_baseType;
              DAST._INewtypeRange _3493___mcc_h513 = _source144.dtor_range;
              bool _3494___mcc_h514 = _source144.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3495___mcc_h515 = _source144.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3496_attributes = _3495___mcc_h515;
              bool _3497_erase = _3494___mcc_h514;
              DAST._INewtypeRange _3498_range = _3493___mcc_h513;
              DAST._IType _3499_b = _3492___mcc_h512;
              {
                RAST._IExpr _out638;
                DCOMP._IOwnership _out639;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out640;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out638, out _out639, out _out640);
                r = _out638;
                resultingOwnership = _out639;
                readIdents = _out640;
              }
            }
          } else if (_source143.is_Nullable) {
            DAST._IType _3500___mcc_h520 = _source143.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out641;
              DCOMP._IOwnership _out642;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out643;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out641, out _out642, out _out643);
              r = _out641;
              resultingOwnership = _out642;
              readIdents = _out643;
            }
          } else if (_source143.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3501___mcc_h522 = _source143.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out644;
              DCOMP._IOwnership _out645;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out646;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out644, out _out645, out _out646);
              r = _out644;
              resultingOwnership = _out645;
              readIdents = _out646;
            }
          } else if (_source143.is_Array) {
            DAST._IType _3502___mcc_h524 = _source143.dtor_element;
            BigInteger _3503___mcc_h525 = _source143.dtor_dims;
            {
              RAST._IExpr _out647;
              DCOMP._IOwnership _out648;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out649;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out647, out _out648, out _out649);
              r = _out647;
              resultingOwnership = _out648;
              readIdents = _out649;
            }
          } else if (_source143.is_Seq) {
            DAST._IType _3504___mcc_h528 = _source143.dtor_element;
            {
              RAST._IExpr _out650;
              DCOMP._IOwnership _out651;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out652;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out650, out _out651, out _out652);
              r = _out650;
              resultingOwnership = _out651;
              readIdents = _out652;
            }
          } else if (_source143.is_Set) {
            DAST._IType _3505___mcc_h530 = _source143.dtor_element;
            {
              RAST._IExpr _out653;
              DCOMP._IOwnership _out654;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out653, out _out654, out _out655);
              r = _out653;
              resultingOwnership = _out654;
              readIdents = _out655;
            }
          } else if (_source143.is_Multiset) {
            DAST._IType _3506___mcc_h532 = _source143.dtor_element;
            {
              RAST._IExpr _out656;
              DCOMP._IOwnership _out657;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out658;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out656, out _out657, out _out658);
              r = _out656;
              resultingOwnership = _out657;
              readIdents = _out658;
            }
          } else if (_source143.is_Map) {
            DAST._IType _3507___mcc_h534 = _source143.dtor_key;
            DAST._IType _3508___mcc_h535 = _source143.dtor_value;
            {
              RAST._IExpr _out659;
              DCOMP._IOwnership _out660;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out661;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out659, out _out660, out _out661);
              r = _out659;
              resultingOwnership = _out660;
              readIdents = _out661;
            }
          } else if (_source143.is_SetBuilder) {
            DAST._IType _3509___mcc_h538 = _source143.dtor_element;
            {
              RAST._IExpr _out662;
              DCOMP._IOwnership _out663;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out664;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out662, out _out663, out _out664);
              r = _out662;
              resultingOwnership = _out663;
              readIdents = _out664;
            }
          } else if (_source143.is_MapBuilder) {
            DAST._IType _3510___mcc_h540 = _source143.dtor_key;
            DAST._IType _3511___mcc_h541 = _source143.dtor_value;
            {
              RAST._IExpr _out665;
              DCOMP._IOwnership _out666;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out667;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out665, out _out666, out _out667);
              r = _out665;
              resultingOwnership = _out666;
              readIdents = _out667;
            }
          } else if (_source143.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3512___mcc_h544 = _source143.dtor_args;
            DAST._IType _3513___mcc_h545 = _source143.dtor_result;
            {
              RAST._IExpr _out668;
              DCOMP._IOwnership _out669;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out670;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out668, out _out669, out _out670);
              r = _out668;
              resultingOwnership = _out669;
              readIdents = _out670;
            }
          } else if (_source143.is_Primitive) {
            DAST._IPrimitive _3514___mcc_h548 = _source143.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out671;
              DCOMP._IOwnership _out672;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out673;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out671, out _out672, out _out673);
              r = _out671;
              resultingOwnership = _out672;
              readIdents = _out673;
            }
          } else if (_source143.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3515___mcc_h550 = _source143.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out674;
              DCOMP._IOwnership _out675;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out676;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out674, out _out675, out _out676);
              r = _out674;
              resultingOwnership = _out675;
              readIdents = _out676;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3516___mcc_h552 = _source143.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out677;
              DCOMP._IOwnership _out678;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out679;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out677, out _out678, out _out679);
              r = _out677;
              resultingOwnership = _out678;
              readIdents = _out679;
            }
          }
        } else if (_source127.is_Multiset) {
          DAST._IType _3517___mcc_h554 = _source127.dtor_element;
          DAST._IType _source145 = _3200___mcc_h1;
          if (_source145.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3518___mcc_h558 = _source145.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3519___mcc_h559 = _source145.dtor_typeArgs;
            DAST._IResolvedType _3520___mcc_h560 = _source145.dtor_resolved;
            DAST._IResolvedType _source146 = _3520___mcc_h560;
            if (_source146.is_Datatype) {
              DAST._IDatatypeType _3521___mcc_h564 = _source146.dtor_datatypeType;
              {
                RAST._IExpr _out680;
                DCOMP._IOwnership _out681;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out682;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out680, out _out681, out _out682);
                r = _out680;
                resultingOwnership = _out681;
                readIdents = _out682;
              }
            } else if (_source146.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3522___mcc_h566 = _source146.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3523___mcc_h567 = _source146.dtor_attributes;
              {
                RAST._IExpr _out683;
                DCOMP._IOwnership _out684;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out685;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out683, out _out684, out _out685);
                r = _out683;
                resultingOwnership = _out684;
                readIdents = _out685;
              }
            } else {
              DAST._IType _3524___mcc_h570 = _source146.dtor_baseType;
              DAST._INewtypeRange _3525___mcc_h571 = _source146.dtor_range;
              bool _3526___mcc_h572 = _source146.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3527___mcc_h573 = _source146.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3528_attributes = _3527___mcc_h573;
              bool _3529_erase = _3526___mcc_h572;
              DAST._INewtypeRange _3530_range = _3525___mcc_h571;
              DAST._IType _3531_b = _3524___mcc_h570;
              {
                RAST._IExpr _out686;
                DCOMP._IOwnership _out687;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out688;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out686, out _out687, out _out688);
                r = _out686;
                resultingOwnership = _out687;
                readIdents = _out688;
              }
            }
          } else if (_source145.is_Nullable) {
            DAST._IType _3532___mcc_h578 = _source145.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out689;
              DCOMP._IOwnership _out690;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out691;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out689, out _out690, out _out691);
              r = _out689;
              resultingOwnership = _out690;
              readIdents = _out691;
            }
          } else if (_source145.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3533___mcc_h580 = _source145.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out692;
              DCOMP._IOwnership _out693;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out694;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out692, out _out693, out _out694);
              r = _out692;
              resultingOwnership = _out693;
              readIdents = _out694;
            }
          } else if (_source145.is_Array) {
            DAST._IType _3534___mcc_h582 = _source145.dtor_element;
            BigInteger _3535___mcc_h583 = _source145.dtor_dims;
            {
              RAST._IExpr _out695;
              DCOMP._IOwnership _out696;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out697;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out695, out _out696, out _out697);
              r = _out695;
              resultingOwnership = _out696;
              readIdents = _out697;
            }
          } else if (_source145.is_Seq) {
            DAST._IType _3536___mcc_h586 = _source145.dtor_element;
            {
              RAST._IExpr _out698;
              DCOMP._IOwnership _out699;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out700;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out698, out _out699, out _out700);
              r = _out698;
              resultingOwnership = _out699;
              readIdents = _out700;
            }
          } else if (_source145.is_Set) {
            DAST._IType _3537___mcc_h588 = _source145.dtor_element;
            {
              RAST._IExpr _out701;
              DCOMP._IOwnership _out702;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out703;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out701, out _out702, out _out703);
              r = _out701;
              resultingOwnership = _out702;
              readIdents = _out703;
            }
          } else if (_source145.is_Multiset) {
            DAST._IType _3538___mcc_h590 = _source145.dtor_element;
            {
              RAST._IExpr _out704;
              DCOMP._IOwnership _out705;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out706;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out704, out _out705, out _out706);
              r = _out704;
              resultingOwnership = _out705;
              readIdents = _out706;
            }
          } else if (_source145.is_Map) {
            DAST._IType _3539___mcc_h592 = _source145.dtor_key;
            DAST._IType _3540___mcc_h593 = _source145.dtor_value;
            {
              RAST._IExpr _out707;
              DCOMP._IOwnership _out708;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out709;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out707, out _out708, out _out709);
              r = _out707;
              resultingOwnership = _out708;
              readIdents = _out709;
            }
          } else if (_source145.is_SetBuilder) {
            DAST._IType _3541___mcc_h596 = _source145.dtor_element;
            {
              RAST._IExpr _out710;
              DCOMP._IOwnership _out711;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out712;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out710, out _out711, out _out712);
              r = _out710;
              resultingOwnership = _out711;
              readIdents = _out712;
            }
          } else if (_source145.is_MapBuilder) {
            DAST._IType _3542___mcc_h598 = _source145.dtor_key;
            DAST._IType _3543___mcc_h599 = _source145.dtor_value;
            {
              RAST._IExpr _out713;
              DCOMP._IOwnership _out714;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out715;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out713, out _out714, out _out715);
              r = _out713;
              resultingOwnership = _out714;
              readIdents = _out715;
            }
          } else if (_source145.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3544___mcc_h602 = _source145.dtor_args;
            DAST._IType _3545___mcc_h603 = _source145.dtor_result;
            {
              RAST._IExpr _out716;
              DCOMP._IOwnership _out717;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out718;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out716, out _out717, out _out718);
              r = _out716;
              resultingOwnership = _out717;
              readIdents = _out718;
            }
          } else if (_source145.is_Primitive) {
            DAST._IPrimitive _3546___mcc_h606 = _source145.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out719;
              DCOMP._IOwnership _out720;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out721;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out719, out _out720, out _out721);
              r = _out719;
              resultingOwnership = _out720;
              readIdents = _out721;
            }
          } else if (_source145.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3547___mcc_h608 = _source145.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out722;
              DCOMP._IOwnership _out723;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out724;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out722, out _out723, out _out724);
              r = _out722;
              resultingOwnership = _out723;
              readIdents = _out724;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3548___mcc_h610 = _source145.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out725;
              DCOMP._IOwnership _out726;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out727;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out725, out _out726, out _out727);
              r = _out725;
              resultingOwnership = _out726;
              readIdents = _out727;
            }
          }
        } else if (_source127.is_Map) {
          DAST._IType _3549___mcc_h612 = _source127.dtor_key;
          DAST._IType _3550___mcc_h613 = _source127.dtor_value;
          DAST._IType _source147 = _3200___mcc_h1;
          if (_source147.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3551___mcc_h620 = _source147.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3552___mcc_h621 = _source147.dtor_typeArgs;
            DAST._IResolvedType _3553___mcc_h622 = _source147.dtor_resolved;
            DAST._IResolvedType _source148 = _3553___mcc_h622;
            if (_source148.is_Datatype) {
              DAST._IDatatypeType _3554___mcc_h626 = _source148.dtor_datatypeType;
              {
                RAST._IExpr _out728;
                DCOMP._IOwnership _out729;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out730;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out728, out _out729, out _out730);
                r = _out728;
                resultingOwnership = _out729;
                readIdents = _out730;
              }
            } else if (_source148.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3555___mcc_h628 = _source148.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3556___mcc_h629 = _source148.dtor_attributes;
              {
                RAST._IExpr _out731;
                DCOMP._IOwnership _out732;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out733;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out731, out _out732, out _out733);
                r = _out731;
                resultingOwnership = _out732;
                readIdents = _out733;
              }
            } else {
              DAST._IType _3557___mcc_h632 = _source148.dtor_baseType;
              DAST._INewtypeRange _3558___mcc_h633 = _source148.dtor_range;
              bool _3559___mcc_h634 = _source148.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3560___mcc_h635 = _source148.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3561_attributes = _3560___mcc_h635;
              bool _3562_erase = _3559___mcc_h634;
              DAST._INewtypeRange _3563_range = _3558___mcc_h633;
              DAST._IType _3564_b = _3557___mcc_h632;
              {
                RAST._IExpr _out734;
                DCOMP._IOwnership _out735;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out736;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out734, out _out735, out _out736);
                r = _out734;
                resultingOwnership = _out735;
                readIdents = _out736;
              }
            }
          } else if (_source147.is_Nullable) {
            DAST._IType _3565___mcc_h640 = _source147.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out737;
              DCOMP._IOwnership _out738;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out739;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out737, out _out738, out _out739);
              r = _out737;
              resultingOwnership = _out738;
              readIdents = _out739;
            }
          } else if (_source147.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3566___mcc_h642 = _source147.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out740;
              DCOMP._IOwnership _out741;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out742;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out740, out _out741, out _out742);
              r = _out740;
              resultingOwnership = _out741;
              readIdents = _out742;
            }
          } else if (_source147.is_Array) {
            DAST._IType _3567___mcc_h644 = _source147.dtor_element;
            BigInteger _3568___mcc_h645 = _source147.dtor_dims;
            {
              RAST._IExpr _out743;
              DCOMP._IOwnership _out744;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out745;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out743, out _out744, out _out745);
              r = _out743;
              resultingOwnership = _out744;
              readIdents = _out745;
            }
          } else if (_source147.is_Seq) {
            DAST._IType _3569___mcc_h648 = _source147.dtor_element;
            {
              RAST._IExpr _out746;
              DCOMP._IOwnership _out747;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out748;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out746, out _out747, out _out748);
              r = _out746;
              resultingOwnership = _out747;
              readIdents = _out748;
            }
          } else if (_source147.is_Set) {
            DAST._IType _3570___mcc_h650 = _source147.dtor_element;
            {
              RAST._IExpr _out749;
              DCOMP._IOwnership _out750;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out751;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out749, out _out750, out _out751);
              r = _out749;
              resultingOwnership = _out750;
              readIdents = _out751;
            }
          } else if (_source147.is_Multiset) {
            DAST._IType _3571___mcc_h652 = _source147.dtor_element;
            {
              RAST._IExpr _out752;
              DCOMP._IOwnership _out753;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out754;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out752, out _out753, out _out754);
              r = _out752;
              resultingOwnership = _out753;
              readIdents = _out754;
            }
          } else if (_source147.is_Map) {
            DAST._IType _3572___mcc_h654 = _source147.dtor_key;
            DAST._IType _3573___mcc_h655 = _source147.dtor_value;
            {
              RAST._IExpr _out755;
              DCOMP._IOwnership _out756;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out757;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out755, out _out756, out _out757);
              r = _out755;
              resultingOwnership = _out756;
              readIdents = _out757;
            }
          } else if (_source147.is_SetBuilder) {
            DAST._IType _3574___mcc_h658 = _source147.dtor_element;
            {
              RAST._IExpr _out758;
              DCOMP._IOwnership _out759;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out760;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out758, out _out759, out _out760);
              r = _out758;
              resultingOwnership = _out759;
              readIdents = _out760;
            }
          } else if (_source147.is_MapBuilder) {
            DAST._IType _3575___mcc_h660 = _source147.dtor_key;
            DAST._IType _3576___mcc_h661 = _source147.dtor_value;
            {
              RAST._IExpr _out761;
              DCOMP._IOwnership _out762;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out763;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out761, out _out762, out _out763);
              r = _out761;
              resultingOwnership = _out762;
              readIdents = _out763;
            }
          } else if (_source147.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3577___mcc_h664 = _source147.dtor_args;
            DAST._IType _3578___mcc_h665 = _source147.dtor_result;
            {
              RAST._IExpr _out764;
              DCOMP._IOwnership _out765;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out766;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out764, out _out765, out _out766);
              r = _out764;
              resultingOwnership = _out765;
              readIdents = _out766;
            }
          } else if (_source147.is_Primitive) {
            DAST._IPrimitive _3579___mcc_h668 = _source147.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out767;
              DCOMP._IOwnership _out768;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out769;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out767, out _out768, out _out769);
              r = _out767;
              resultingOwnership = _out768;
              readIdents = _out769;
            }
          } else if (_source147.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3580___mcc_h670 = _source147.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out770;
              DCOMP._IOwnership _out771;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out772;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out770, out _out771, out _out772);
              r = _out770;
              resultingOwnership = _out771;
              readIdents = _out772;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3581___mcc_h672 = _source147.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out773;
              DCOMP._IOwnership _out774;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out775;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out773, out _out774, out _out775);
              r = _out773;
              resultingOwnership = _out774;
              readIdents = _out775;
            }
          }
        } else if (_source127.is_SetBuilder) {
          DAST._IType _3582___mcc_h674 = _source127.dtor_element;
          DAST._IType _source149 = _3200___mcc_h1;
          if (_source149.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3583___mcc_h678 = _source149.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3584___mcc_h679 = _source149.dtor_typeArgs;
            DAST._IResolvedType _3585___mcc_h680 = _source149.dtor_resolved;
            DAST._IResolvedType _source150 = _3585___mcc_h680;
            if (_source150.is_Datatype) {
              DAST._IDatatypeType _3586___mcc_h684 = _source150.dtor_datatypeType;
              {
                RAST._IExpr _out776;
                DCOMP._IOwnership _out777;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out778;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out776, out _out777, out _out778);
                r = _out776;
                resultingOwnership = _out777;
                readIdents = _out778;
              }
            } else if (_source150.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3587___mcc_h686 = _source150.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3588___mcc_h687 = _source150.dtor_attributes;
              {
                RAST._IExpr _out779;
                DCOMP._IOwnership _out780;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out781;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out779, out _out780, out _out781);
                r = _out779;
                resultingOwnership = _out780;
                readIdents = _out781;
              }
            } else {
              DAST._IType _3589___mcc_h690 = _source150.dtor_baseType;
              DAST._INewtypeRange _3590___mcc_h691 = _source150.dtor_range;
              bool _3591___mcc_h692 = _source150.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3592___mcc_h693 = _source150.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3593_attributes = _3592___mcc_h693;
              bool _3594_erase = _3591___mcc_h692;
              DAST._INewtypeRange _3595_range = _3590___mcc_h691;
              DAST._IType _3596_b = _3589___mcc_h690;
              {
                RAST._IExpr _out782;
                DCOMP._IOwnership _out783;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out784;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out782, out _out783, out _out784);
                r = _out782;
                resultingOwnership = _out783;
                readIdents = _out784;
              }
            }
          } else if (_source149.is_Nullable) {
            DAST._IType _3597___mcc_h698 = _source149.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out785;
              DCOMP._IOwnership _out786;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out787;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out785, out _out786, out _out787);
              r = _out785;
              resultingOwnership = _out786;
              readIdents = _out787;
            }
          } else if (_source149.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3598___mcc_h700 = _source149.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out788;
              DCOMP._IOwnership _out789;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out790;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out788, out _out789, out _out790);
              r = _out788;
              resultingOwnership = _out789;
              readIdents = _out790;
            }
          } else if (_source149.is_Array) {
            DAST._IType _3599___mcc_h702 = _source149.dtor_element;
            BigInteger _3600___mcc_h703 = _source149.dtor_dims;
            {
              RAST._IExpr _out791;
              DCOMP._IOwnership _out792;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out793;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out791, out _out792, out _out793);
              r = _out791;
              resultingOwnership = _out792;
              readIdents = _out793;
            }
          } else if (_source149.is_Seq) {
            DAST._IType _3601___mcc_h706 = _source149.dtor_element;
            {
              RAST._IExpr _out794;
              DCOMP._IOwnership _out795;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out796;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out794, out _out795, out _out796);
              r = _out794;
              resultingOwnership = _out795;
              readIdents = _out796;
            }
          } else if (_source149.is_Set) {
            DAST._IType _3602___mcc_h708 = _source149.dtor_element;
            {
              RAST._IExpr _out797;
              DCOMP._IOwnership _out798;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out799;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out797, out _out798, out _out799);
              r = _out797;
              resultingOwnership = _out798;
              readIdents = _out799;
            }
          } else if (_source149.is_Multiset) {
            DAST._IType _3603___mcc_h710 = _source149.dtor_element;
            {
              RAST._IExpr _out800;
              DCOMP._IOwnership _out801;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out802;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out800, out _out801, out _out802);
              r = _out800;
              resultingOwnership = _out801;
              readIdents = _out802;
            }
          } else if (_source149.is_Map) {
            DAST._IType _3604___mcc_h712 = _source149.dtor_key;
            DAST._IType _3605___mcc_h713 = _source149.dtor_value;
            {
              RAST._IExpr _out803;
              DCOMP._IOwnership _out804;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out805;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out803, out _out804, out _out805);
              r = _out803;
              resultingOwnership = _out804;
              readIdents = _out805;
            }
          } else if (_source149.is_SetBuilder) {
            DAST._IType _3606___mcc_h716 = _source149.dtor_element;
            {
              RAST._IExpr _out806;
              DCOMP._IOwnership _out807;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out808;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out806, out _out807, out _out808);
              r = _out806;
              resultingOwnership = _out807;
              readIdents = _out808;
            }
          } else if (_source149.is_MapBuilder) {
            DAST._IType _3607___mcc_h718 = _source149.dtor_key;
            DAST._IType _3608___mcc_h719 = _source149.dtor_value;
            {
              RAST._IExpr _out809;
              DCOMP._IOwnership _out810;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out811;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out809, out _out810, out _out811);
              r = _out809;
              resultingOwnership = _out810;
              readIdents = _out811;
            }
          } else if (_source149.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3609___mcc_h722 = _source149.dtor_args;
            DAST._IType _3610___mcc_h723 = _source149.dtor_result;
            {
              RAST._IExpr _out812;
              DCOMP._IOwnership _out813;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out814;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out812, out _out813, out _out814);
              r = _out812;
              resultingOwnership = _out813;
              readIdents = _out814;
            }
          } else if (_source149.is_Primitive) {
            DAST._IPrimitive _3611___mcc_h726 = _source149.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out815;
              DCOMP._IOwnership _out816;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out817;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out815, out _out816, out _out817);
              r = _out815;
              resultingOwnership = _out816;
              readIdents = _out817;
            }
          } else if (_source149.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3612___mcc_h728 = _source149.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out818;
              DCOMP._IOwnership _out819;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out820;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out818, out _out819, out _out820);
              r = _out818;
              resultingOwnership = _out819;
              readIdents = _out820;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3613___mcc_h730 = _source149.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out821;
              DCOMP._IOwnership _out822;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out823;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out821, out _out822, out _out823);
              r = _out821;
              resultingOwnership = _out822;
              readIdents = _out823;
            }
          }
        } else if (_source127.is_MapBuilder) {
          DAST._IType _3614___mcc_h732 = _source127.dtor_key;
          DAST._IType _3615___mcc_h733 = _source127.dtor_value;
          DAST._IType _source151 = _3200___mcc_h1;
          if (_source151.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3616___mcc_h740 = _source151.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3617___mcc_h741 = _source151.dtor_typeArgs;
            DAST._IResolvedType _3618___mcc_h742 = _source151.dtor_resolved;
            DAST._IResolvedType _source152 = _3618___mcc_h742;
            if (_source152.is_Datatype) {
              DAST._IDatatypeType _3619___mcc_h746 = _source152.dtor_datatypeType;
              {
                RAST._IExpr _out824;
                DCOMP._IOwnership _out825;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out826;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out824, out _out825, out _out826);
                r = _out824;
                resultingOwnership = _out825;
                readIdents = _out826;
              }
            } else if (_source152.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3620___mcc_h748 = _source152.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3621___mcc_h749 = _source152.dtor_attributes;
              {
                RAST._IExpr _out827;
                DCOMP._IOwnership _out828;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out829;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out827, out _out828, out _out829);
                r = _out827;
                resultingOwnership = _out828;
                readIdents = _out829;
              }
            } else {
              DAST._IType _3622___mcc_h752 = _source152.dtor_baseType;
              DAST._INewtypeRange _3623___mcc_h753 = _source152.dtor_range;
              bool _3624___mcc_h754 = _source152.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3625___mcc_h755 = _source152.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3626_attributes = _3625___mcc_h755;
              bool _3627_erase = _3624___mcc_h754;
              DAST._INewtypeRange _3628_range = _3623___mcc_h753;
              DAST._IType _3629_b = _3622___mcc_h752;
              {
                RAST._IExpr _out830;
                DCOMP._IOwnership _out831;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out832;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out830, out _out831, out _out832);
                r = _out830;
                resultingOwnership = _out831;
                readIdents = _out832;
              }
            }
          } else if (_source151.is_Nullable) {
            DAST._IType _3630___mcc_h760 = _source151.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out833;
              DCOMP._IOwnership _out834;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out835;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out833, out _out834, out _out835);
              r = _out833;
              resultingOwnership = _out834;
              readIdents = _out835;
            }
          } else if (_source151.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3631___mcc_h762 = _source151.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out836;
              DCOMP._IOwnership _out837;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out838;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out836, out _out837, out _out838);
              r = _out836;
              resultingOwnership = _out837;
              readIdents = _out838;
            }
          } else if (_source151.is_Array) {
            DAST._IType _3632___mcc_h764 = _source151.dtor_element;
            BigInteger _3633___mcc_h765 = _source151.dtor_dims;
            {
              RAST._IExpr _out839;
              DCOMP._IOwnership _out840;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out841;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out839, out _out840, out _out841);
              r = _out839;
              resultingOwnership = _out840;
              readIdents = _out841;
            }
          } else if (_source151.is_Seq) {
            DAST._IType _3634___mcc_h768 = _source151.dtor_element;
            {
              RAST._IExpr _out842;
              DCOMP._IOwnership _out843;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out844;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out842, out _out843, out _out844);
              r = _out842;
              resultingOwnership = _out843;
              readIdents = _out844;
            }
          } else if (_source151.is_Set) {
            DAST._IType _3635___mcc_h770 = _source151.dtor_element;
            {
              RAST._IExpr _out845;
              DCOMP._IOwnership _out846;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out847;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out845, out _out846, out _out847);
              r = _out845;
              resultingOwnership = _out846;
              readIdents = _out847;
            }
          } else if (_source151.is_Multiset) {
            DAST._IType _3636___mcc_h772 = _source151.dtor_element;
            {
              RAST._IExpr _out848;
              DCOMP._IOwnership _out849;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out850;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out848, out _out849, out _out850);
              r = _out848;
              resultingOwnership = _out849;
              readIdents = _out850;
            }
          } else if (_source151.is_Map) {
            DAST._IType _3637___mcc_h774 = _source151.dtor_key;
            DAST._IType _3638___mcc_h775 = _source151.dtor_value;
            {
              RAST._IExpr _out851;
              DCOMP._IOwnership _out852;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out853;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out851, out _out852, out _out853);
              r = _out851;
              resultingOwnership = _out852;
              readIdents = _out853;
            }
          } else if (_source151.is_SetBuilder) {
            DAST._IType _3639___mcc_h778 = _source151.dtor_element;
            {
              RAST._IExpr _out854;
              DCOMP._IOwnership _out855;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out856;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out854, out _out855, out _out856);
              r = _out854;
              resultingOwnership = _out855;
              readIdents = _out856;
            }
          } else if (_source151.is_MapBuilder) {
            DAST._IType _3640___mcc_h780 = _source151.dtor_key;
            DAST._IType _3641___mcc_h781 = _source151.dtor_value;
            {
              RAST._IExpr _out857;
              DCOMP._IOwnership _out858;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out859;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out857, out _out858, out _out859);
              r = _out857;
              resultingOwnership = _out858;
              readIdents = _out859;
            }
          } else if (_source151.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3642___mcc_h784 = _source151.dtor_args;
            DAST._IType _3643___mcc_h785 = _source151.dtor_result;
            {
              RAST._IExpr _out860;
              DCOMP._IOwnership _out861;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out862;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out860, out _out861, out _out862);
              r = _out860;
              resultingOwnership = _out861;
              readIdents = _out862;
            }
          } else if (_source151.is_Primitive) {
            DAST._IPrimitive _3644___mcc_h788 = _source151.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out863;
              DCOMP._IOwnership _out864;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out865;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out863, out _out864, out _out865);
              r = _out863;
              resultingOwnership = _out864;
              readIdents = _out865;
            }
          } else if (_source151.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3645___mcc_h790 = _source151.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out866;
              DCOMP._IOwnership _out867;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out868;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out866, out _out867, out _out868);
              r = _out866;
              resultingOwnership = _out867;
              readIdents = _out868;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3646___mcc_h792 = _source151.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out869;
              DCOMP._IOwnership _out870;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out871;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out869, out _out870, out _out871);
              r = _out869;
              resultingOwnership = _out870;
              readIdents = _out871;
            }
          }
        } else if (_source127.is_Arrow) {
          Dafny.ISequence<DAST._IType> _3647___mcc_h794 = _source127.dtor_args;
          DAST._IType _3648___mcc_h795 = _source127.dtor_result;
          DAST._IType _source153 = _3200___mcc_h1;
          if (_source153.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3649___mcc_h802 = _source153.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3650___mcc_h803 = _source153.dtor_typeArgs;
            DAST._IResolvedType _3651___mcc_h804 = _source153.dtor_resolved;
            DAST._IResolvedType _source154 = _3651___mcc_h804;
            if (_source154.is_Datatype) {
              DAST._IDatatypeType _3652___mcc_h808 = _source154.dtor_datatypeType;
              {
                RAST._IExpr _out872;
                DCOMP._IOwnership _out873;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out874;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out872, out _out873, out _out874);
                r = _out872;
                resultingOwnership = _out873;
                readIdents = _out874;
              }
            } else if (_source154.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3653___mcc_h810 = _source154.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3654___mcc_h811 = _source154.dtor_attributes;
              {
                RAST._IExpr _out875;
                DCOMP._IOwnership _out876;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out877;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out875, out _out876, out _out877);
                r = _out875;
                resultingOwnership = _out876;
                readIdents = _out877;
              }
            } else {
              DAST._IType _3655___mcc_h814 = _source154.dtor_baseType;
              DAST._INewtypeRange _3656___mcc_h815 = _source154.dtor_range;
              bool _3657___mcc_h816 = _source154.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3658___mcc_h817 = _source154.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3659_attributes = _3658___mcc_h817;
              bool _3660_erase = _3657___mcc_h816;
              DAST._INewtypeRange _3661_range = _3656___mcc_h815;
              DAST._IType _3662_b = _3655___mcc_h814;
              {
                RAST._IExpr _out878;
                DCOMP._IOwnership _out879;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out880;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out878, out _out879, out _out880);
                r = _out878;
                resultingOwnership = _out879;
                readIdents = _out880;
              }
            }
          } else if (_source153.is_Nullable) {
            DAST._IType _3663___mcc_h822 = _source153.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out881;
              DCOMP._IOwnership _out882;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out883;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out881, out _out882, out _out883);
              r = _out881;
              resultingOwnership = _out882;
              readIdents = _out883;
            }
          } else if (_source153.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3664___mcc_h824 = _source153.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out884;
              DCOMP._IOwnership _out885;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out886;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out884, out _out885, out _out886);
              r = _out884;
              resultingOwnership = _out885;
              readIdents = _out886;
            }
          } else if (_source153.is_Array) {
            DAST._IType _3665___mcc_h826 = _source153.dtor_element;
            BigInteger _3666___mcc_h827 = _source153.dtor_dims;
            {
              RAST._IExpr _out887;
              DCOMP._IOwnership _out888;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out889;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out887, out _out888, out _out889);
              r = _out887;
              resultingOwnership = _out888;
              readIdents = _out889;
            }
          } else if (_source153.is_Seq) {
            DAST._IType _3667___mcc_h830 = _source153.dtor_element;
            {
              RAST._IExpr _out890;
              DCOMP._IOwnership _out891;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out892;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out890, out _out891, out _out892);
              r = _out890;
              resultingOwnership = _out891;
              readIdents = _out892;
            }
          } else if (_source153.is_Set) {
            DAST._IType _3668___mcc_h832 = _source153.dtor_element;
            {
              RAST._IExpr _out893;
              DCOMP._IOwnership _out894;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out895;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out893, out _out894, out _out895);
              r = _out893;
              resultingOwnership = _out894;
              readIdents = _out895;
            }
          } else if (_source153.is_Multiset) {
            DAST._IType _3669___mcc_h834 = _source153.dtor_element;
            {
              RAST._IExpr _out896;
              DCOMP._IOwnership _out897;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out898;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out896, out _out897, out _out898);
              r = _out896;
              resultingOwnership = _out897;
              readIdents = _out898;
            }
          } else if (_source153.is_Map) {
            DAST._IType _3670___mcc_h836 = _source153.dtor_key;
            DAST._IType _3671___mcc_h837 = _source153.dtor_value;
            {
              RAST._IExpr _out899;
              DCOMP._IOwnership _out900;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out901;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out899, out _out900, out _out901);
              r = _out899;
              resultingOwnership = _out900;
              readIdents = _out901;
            }
          } else if (_source153.is_SetBuilder) {
            DAST._IType _3672___mcc_h840 = _source153.dtor_element;
            {
              RAST._IExpr _out902;
              DCOMP._IOwnership _out903;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out904;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out902, out _out903, out _out904);
              r = _out902;
              resultingOwnership = _out903;
              readIdents = _out904;
            }
          } else if (_source153.is_MapBuilder) {
            DAST._IType _3673___mcc_h842 = _source153.dtor_key;
            DAST._IType _3674___mcc_h843 = _source153.dtor_value;
            {
              RAST._IExpr _out905;
              DCOMP._IOwnership _out906;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out907;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out905, out _out906, out _out907);
              r = _out905;
              resultingOwnership = _out906;
              readIdents = _out907;
            }
          } else if (_source153.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3675___mcc_h846 = _source153.dtor_args;
            DAST._IType _3676___mcc_h847 = _source153.dtor_result;
            {
              RAST._IExpr _out908;
              DCOMP._IOwnership _out909;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out910;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out908, out _out909, out _out910);
              r = _out908;
              resultingOwnership = _out909;
              readIdents = _out910;
            }
          } else if (_source153.is_Primitive) {
            DAST._IPrimitive _3677___mcc_h850 = _source153.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out911;
              DCOMP._IOwnership _out912;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out913;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out911, out _out912, out _out913);
              r = _out911;
              resultingOwnership = _out912;
              readIdents = _out913;
            }
          } else if (_source153.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3678___mcc_h852 = _source153.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out914;
              DCOMP._IOwnership _out915;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out916;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out914, out _out915, out _out916);
              r = _out914;
              resultingOwnership = _out915;
              readIdents = _out916;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3679___mcc_h854 = _source153.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out917;
              DCOMP._IOwnership _out918;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out919;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out917, out _out918, out _out919);
              r = _out917;
              resultingOwnership = _out918;
              readIdents = _out919;
            }
          }
        } else if (_source127.is_Primitive) {
          DAST._IPrimitive _3680___mcc_h856 = _source127.dtor_Primitive_i_a0;
          DAST._IPrimitive _source155 = _3680___mcc_h856;
          if (_source155.is_Int) {
            DAST._IType _source156 = _3200___mcc_h1;
            if (_source156.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3681___mcc_h860 = _source156.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3682___mcc_h861 = _source156.dtor_typeArgs;
              DAST._IResolvedType _3683___mcc_h862 = _source156.dtor_resolved;
              DAST._IResolvedType _source157 = _3683___mcc_h862;
              if (_source157.is_Datatype) {
                DAST._IDatatypeType _3684___mcc_h866 = _source157.dtor_datatypeType;
                {
                  RAST._IExpr _out920;
                  DCOMP._IOwnership _out921;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out922;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out920, out _out921, out _out922);
                  r = _out920;
                  resultingOwnership = _out921;
                  readIdents = _out922;
                }
              } else if (_source157.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3685___mcc_h868 = _source157.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3686___mcc_h869 = _source157.dtor_attributes;
                {
                  RAST._IExpr _out923;
                  DCOMP._IOwnership _out924;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out925;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out923, out _out924, out _out925);
                  r = _out923;
                  resultingOwnership = _out924;
                  readIdents = _out925;
                }
              } else {
                DAST._IType _3687___mcc_h872 = _source157.dtor_baseType;
                DAST._INewtypeRange _3688___mcc_h873 = _source157.dtor_range;
                bool _3689___mcc_h874 = _source157.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3690___mcc_h875 = _source157.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3691_attributes = _3690___mcc_h875;
                bool _3692_erase = _3689___mcc_h874;
                DAST._INewtypeRange _3693_range = _3688___mcc_h873;
                DAST._IType _3694_b = _3687___mcc_h872;
                {
                  RAST._IExpr _out926;
                  DCOMP._IOwnership _out927;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out928;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out926, out _out927, out _out928);
                  r = _out926;
                  resultingOwnership = _out927;
                  readIdents = _out928;
                }
              }
            } else if (_source156.is_Nullable) {
              DAST._IType _3695___mcc_h880 = _source156.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out929;
                DCOMP._IOwnership _out930;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out931;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out929, out _out930, out _out931);
                r = _out929;
                resultingOwnership = _out930;
                readIdents = _out931;
              }
            } else if (_source156.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3696___mcc_h882 = _source156.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out932;
                DCOMP._IOwnership _out933;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out934;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out932, out _out933, out _out934);
                r = _out932;
                resultingOwnership = _out933;
                readIdents = _out934;
              }
            } else if (_source156.is_Array) {
              DAST._IType _3697___mcc_h884 = _source156.dtor_element;
              BigInteger _3698___mcc_h885 = _source156.dtor_dims;
              {
                RAST._IExpr _out935;
                DCOMP._IOwnership _out936;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out937;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out935, out _out936, out _out937);
                r = _out935;
                resultingOwnership = _out936;
                readIdents = _out937;
              }
            } else if (_source156.is_Seq) {
              DAST._IType _3699___mcc_h888 = _source156.dtor_element;
              {
                RAST._IExpr _out938;
                DCOMP._IOwnership _out939;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out940;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out938, out _out939, out _out940);
                r = _out938;
                resultingOwnership = _out939;
                readIdents = _out940;
              }
            } else if (_source156.is_Set) {
              DAST._IType _3700___mcc_h890 = _source156.dtor_element;
              {
                RAST._IExpr _out941;
                DCOMP._IOwnership _out942;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out943;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out941, out _out942, out _out943);
                r = _out941;
                resultingOwnership = _out942;
                readIdents = _out943;
              }
            } else if (_source156.is_Multiset) {
              DAST._IType _3701___mcc_h892 = _source156.dtor_element;
              {
                RAST._IExpr _out944;
                DCOMP._IOwnership _out945;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out946;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out944, out _out945, out _out946);
                r = _out944;
                resultingOwnership = _out945;
                readIdents = _out946;
              }
            } else if (_source156.is_Map) {
              DAST._IType _3702___mcc_h894 = _source156.dtor_key;
              DAST._IType _3703___mcc_h895 = _source156.dtor_value;
              {
                RAST._IExpr _out947;
                DCOMP._IOwnership _out948;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out949;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out947, out _out948, out _out949);
                r = _out947;
                resultingOwnership = _out948;
                readIdents = _out949;
              }
            } else if (_source156.is_SetBuilder) {
              DAST._IType _3704___mcc_h898 = _source156.dtor_element;
              {
                RAST._IExpr _out950;
                DCOMP._IOwnership _out951;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out952;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out950, out _out951, out _out952);
                r = _out950;
                resultingOwnership = _out951;
                readIdents = _out952;
              }
            } else if (_source156.is_MapBuilder) {
              DAST._IType _3705___mcc_h900 = _source156.dtor_key;
              DAST._IType _3706___mcc_h901 = _source156.dtor_value;
              {
                RAST._IExpr _out953;
                DCOMP._IOwnership _out954;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out955;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out953, out _out954, out _out955);
                r = _out953;
                resultingOwnership = _out954;
                readIdents = _out955;
              }
            } else if (_source156.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3707___mcc_h904 = _source156.dtor_args;
              DAST._IType _3708___mcc_h905 = _source156.dtor_result;
              {
                RAST._IExpr _out956;
                DCOMP._IOwnership _out957;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out958;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out956, out _out957, out _out958);
                r = _out956;
                resultingOwnership = _out957;
                readIdents = _out958;
              }
            } else if (_source156.is_Primitive) {
              DAST._IPrimitive _3709___mcc_h908 = _source156.dtor_Primitive_i_a0;
              DAST._IPrimitive _source158 = _3709___mcc_h908;
              if (_source158.is_Int) {
                {
                  RAST._IExpr _out959;
                  DCOMP._IOwnership _out960;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out961;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out959, out _out960, out _out961);
                  r = _out959;
                  resultingOwnership = _out960;
                  readIdents = _out961;
                }
              } else if (_source158.is_Real) {
                {
                  RAST._IExpr _3710_recursiveGen;
                  DCOMP._IOwnership _3711___v97;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3712_recIdents;
                  RAST._IExpr _out962;
                  DCOMP._IOwnership _out963;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out964;
                  (this).GenExpr(_3193_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out962, out _out963, out _out964);
                  _3710_recursiveGen = _out962;
                  _3711___v97 = _out963;
                  _3712_recIdents = _out964;
                  r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_3710_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                  RAST._IExpr _out965;
                  DCOMP._IOwnership _out966;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out965, out _out966);
                  r = _out965;
                  resultingOwnership = _out966;
                  readIdents = _3712_recIdents;
                }
              } else if (_source158.is_String) {
                {
                  RAST._IExpr _out967;
                  DCOMP._IOwnership _out968;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out969;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out967, out _out968, out _out969);
                  r = _out967;
                  resultingOwnership = _out968;
                  readIdents = _out969;
                }
              } else if (_source158.is_Bool) {
                {
                  RAST._IExpr _out970;
                  DCOMP._IOwnership _out971;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out972;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out970, out _out971, out _out972);
                  r = _out970;
                  resultingOwnership = _out971;
                  readIdents = _out972;
                }
              } else {
                {
                  RAST._IType _3713_rhsType;
                  RAST._IType _out973;
                  _out973 = (this).GenType(_3195_toTpe, true, false);
                  _3713_rhsType = _out973;
                  RAST._IExpr _3714_recursiveGen;
                  DCOMP._IOwnership _3715___v103;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3716_recIdents;
                  RAST._IExpr _out974;
                  DCOMP._IOwnership _out975;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out976;
                  (this).GenExpr(_3193_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out974, out _out975, out _out976);
                  _3714_recursiveGen = _out974;
                  _3715___v103 = _out975;
                  _3716_recIdents = _out976;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), (_3714_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()")));
                  RAST._IExpr _out977;
                  DCOMP._IOwnership _out978;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out977, out _out978);
                  r = _out977;
                  resultingOwnership = _out978;
                  readIdents = _3716_recIdents;
                }
              }
            } else if (_source156.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3717___mcc_h910 = _source156.dtor_Passthrough_i_a0;
              {
                RAST._IType _3718_rhsType;
                RAST._IType _out979;
                _out979 = (this).GenType(_3195_toTpe, true, false);
                _3718_rhsType = _out979;
                RAST._IExpr _3719_recursiveGen;
                DCOMP._IOwnership _3720___v100;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3721_recIdents;
                RAST._IExpr _out980;
                DCOMP._IOwnership _out981;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out982;
                (this).GenExpr(_3193_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out980, out _out981, out _out982);
                _3719_recursiveGen = _out980;
                _3720___v100 = _out981;
                _3721_recIdents = _out982;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_3718_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_3719_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                RAST._IExpr _out983;
                DCOMP._IOwnership _out984;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out983, out _out984);
                r = _out983;
                resultingOwnership = _out984;
                readIdents = _3721_recIdents;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3722___mcc_h912 = _source156.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out985;
                DCOMP._IOwnership _out986;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out987;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out985, out _out986, out _out987);
                r = _out985;
                resultingOwnership = _out986;
                readIdents = _out987;
              }
            }
          } else if (_source155.is_Real) {
            DAST._IType _source159 = _3200___mcc_h1;
            if (_source159.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3723___mcc_h914 = _source159.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3724___mcc_h915 = _source159.dtor_typeArgs;
              DAST._IResolvedType _3725___mcc_h916 = _source159.dtor_resolved;
              DAST._IResolvedType _source160 = _3725___mcc_h916;
              if (_source160.is_Datatype) {
                DAST._IDatatypeType _3726___mcc_h920 = _source160.dtor_datatypeType;
                {
                  RAST._IExpr _out988;
                  DCOMP._IOwnership _out989;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out990;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out988, out _out989, out _out990);
                  r = _out988;
                  resultingOwnership = _out989;
                  readIdents = _out990;
                }
              } else if (_source160.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3727___mcc_h922 = _source160.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3728___mcc_h923 = _source160.dtor_attributes;
                {
                  RAST._IExpr _out991;
                  DCOMP._IOwnership _out992;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out993;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out991, out _out992, out _out993);
                  r = _out991;
                  resultingOwnership = _out992;
                  readIdents = _out993;
                }
              } else {
                DAST._IType _3729___mcc_h926 = _source160.dtor_baseType;
                DAST._INewtypeRange _3730___mcc_h927 = _source160.dtor_range;
                bool _3731___mcc_h928 = _source160.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3732___mcc_h929 = _source160.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3733_attributes = _3732___mcc_h929;
                bool _3734_erase = _3731___mcc_h928;
                DAST._INewtypeRange _3735_range = _3730___mcc_h927;
                DAST._IType _3736_b = _3729___mcc_h926;
                {
                  RAST._IExpr _out994;
                  DCOMP._IOwnership _out995;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out996;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out994, out _out995, out _out996);
                  r = _out994;
                  resultingOwnership = _out995;
                  readIdents = _out996;
                }
              }
            } else if (_source159.is_Nullable) {
              DAST._IType _3737___mcc_h934 = _source159.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out997;
                DCOMP._IOwnership _out998;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out999;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out997, out _out998, out _out999);
                r = _out997;
                resultingOwnership = _out998;
                readIdents = _out999;
              }
            } else if (_source159.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3738___mcc_h936 = _source159.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out1000;
                DCOMP._IOwnership _out1001;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1002;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1000, out _out1001, out _out1002);
                r = _out1000;
                resultingOwnership = _out1001;
                readIdents = _out1002;
              }
            } else if (_source159.is_Array) {
              DAST._IType _3739___mcc_h938 = _source159.dtor_element;
              BigInteger _3740___mcc_h939 = _source159.dtor_dims;
              {
                RAST._IExpr _out1003;
                DCOMP._IOwnership _out1004;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1005;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1003, out _out1004, out _out1005);
                r = _out1003;
                resultingOwnership = _out1004;
                readIdents = _out1005;
              }
            } else if (_source159.is_Seq) {
              DAST._IType _3741___mcc_h942 = _source159.dtor_element;
              {
                RAST._IExpr _out1006;
                DCOMP._IOwnership _out1007;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1008;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1006, out _out1007, out _out1008);
                r = _out1006;
                resultingOwnership = _out1007;
                readIdents = _out1008;
              }
            } else if (_source159.is_Set) {
              DAST._IType _3742___mcc_h944 = _source159.dtor_element;
              {
                RAST._IExpr _out1009;
                DCOMP._IOwnership _out1010;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1011;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1009, out _out1010, out _out1011);
                r = _out1009;
                resultingOwnership = _out1010;
                readIdents = _out1011;
              }
            } else if (_source159.is_Multiset) {
              DAST._IType _3743___mcc_h946 = _source159.dtor_element;
              {
                RAST._IExpr _out1012;
                DCOMP._IOwnership _out1013;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1014;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1012, out _out1013, out _out1014);
                r = _out1012;
                resultingOwnership = _out1013;
                readIdents = _out1014;
              }
            } else if (_source159.is_Map) {
              DAST._IType _3744___mcc_h948 = _source159.dtor_key;
              DAST._IType _3745___mcc_h949 = _source159.dtor_value;
              {
                RAST._IExpr _out1015;
                DCOMP._IOwnership _out1016;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1017;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1015, out _out1016, out _out1017);
                r = _out1015;
                resultingOwnership = _out1016;
                readIdents = _out1017;
              }
            } else if (_source159.is_SetBuilder) {
              DAST._IType _3746___mcc_h952 = _source159.dtor_element;
              {
                RAST._IExpr _out1018;
                DCOMP._IOwnership _out1019;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1020;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1018, out _out1019, out _out1020);
                r = _out1018;
                resultingOwnership = _out1019;
                readIdents = _out1020;
              }
            } else if (_source159.is_MapBuilder) {
              DAST._IType _3747___mcc_h954 = _source159.dtor_key;
              DAST._IType _3748___mcc_h955 = _source159.dtor_value;
              {
                RAST._IExpr _out1021;
                DCOMP._IOwnership _out1022;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1023;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1021, out _out1022, out _out1023);
                r = _out1021;
                resultingOwnership = _out1022;
                readIdents = _out1023;
              }
            } else if (_source159.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3749___mcc_h958 = _source159.dtor_args;
              DAST._IType _3750___mcc_h959 = _source159.dtor_result;
              {
                RAST._IExpr _out1024;
                DCOMP._IOwnership _out1025;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1026;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1024, out _out1025, out _out1026);
                r = _out1024;
                resultingOwnership = _out1025;
                readIdents = _out1026;
              }
            } else if (_source159.is_Primitive) {
              DAST._IPrimitive _3751___mcc_h962 = _source159.dtor_Primitive_i_a0;
              DAST._IPrimitive _source161 = _3751___mcc_h962;
              if (_source161.is_Int) {
                {
                  RAST._IExpr _3752_recursiveGen;
                  DCOMP._IOwnership _3753___v98;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3754_recIdents;
                  RAST._IExpr _out1027;
                  DCOMP._IOwnership _out1028;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1029;
                  (this).GenExpr(_3193_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1027, out _out1028, out _out1029);
                  _3752_recursiveGen = _out1027;
                  _3753___v98 = _out1028;
                  _3754_recIdents = _out1029;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_3752_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                  RAST._IExpr _out1030;
                  DCOMP._IOwnership _out1031;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1030, out _out1031);
                  r = _out1030;
                  resultingOwnership = _out1031;
                  readIdents = _3754_recIdents;
                }
              } else if (_source161.is_Real) {
                {
                  RAST._IExpr _out1032;
                  DCOMP._IOwnership _out1033;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1034;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1032, out _out1033, out _out1034);
                  r = _out1032;
                  resultingOwnership = _out1033;
                  readIdents = _out1034;
                }
              } else if (_source161.is_String) {
                {
                  RAST._IExpr _out1035;
                  DCOMP._IOwnership _out1036;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1037;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1035, out _out1036, out _out1037);
                  r = _out1035;
                  resultingOwnership = _out1036;
                  readIdents = _out1037;
                }
              } else if (_source161.is_Bool) {
                {
                  RAST._IExpr _out1038;
                  DCOMP._IOwnership _out1039;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1040;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1038, out _out1039, out _out1040);
                  r = _out1038;
                  resultingOwnership = _out1039;
                  readIdents = _out1040;
                }
              } else {
                {
                  RAST._IExpr _out1041;
                  DCOMP._IOwnership _out1042;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1043;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1041, out _out1042, out _out1043);
                  r = _out1041;
                  resultingOwnership = _out1042;
                  readIdents = _out1043;
                }
              }
            } else if (_source159.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3755___mcc_h964 = _source159.dtor_Passthrough_i_a0;
              {
                RAST._IExpr _out1044;
                DCOMP._IOwnership _out1045;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1046;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1044, out _out1045, out _out1046);
                r = _out1044;
                resultingOwnership = _out1045;
                readIdents = _out1046;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3756___mcc_h966 = _source159.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out1047;
                DCOMP._IOwnership _out1048;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1049;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1047, out _out1048, out _out1049);
                r = _out1047;
                resultingOwnership = _out1048;
                readIdents = _out1049;
              }
            }
          } else if (_source155.is_String) {
            DAST._IType _source162 = _3200___mcc_h1;
            if (_source162.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3757___mcc_h968 = _source162.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3758___mcc_h969 = _source162.dtor_typeArgs;
              DAST._IResolvedType _3759___mcc_h970 = _source162.dtor_resolved;
              DAST._IResolvedType _source163 = _3759___mcc_h970;
              if (_source163.is_Datatype) {
                DAST._IDatatypeType _3760___mcc_h974 = _source163.dtor_datatypeType;
                {
                  RAST._IExpr _out1050;
                  DCOMP._IOwnership _out1051;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1052;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1050, out _out1051, out _out1052);
                  r = _out1050;
                  resultingOwnership = _out1051;
                  readIdents = _out1052;
                }
              } else if (_source163.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3761___mcc_h976 = _source163.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3762___mcc_h977 = _source163.dtor_attributes;
                {
                  RAST._IExpr _out1053;
                  DCOMP._IOwnership _out1054;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1055;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1053, out _out1054, out _out1055);
                  r = _out1053;
                  resultingOwnership = _out1054;
                  readIdents = _out1055;
                }
              } else {
                DAST._IType _3763___mcc_h980 = _source163.dtor_baseType;
                DAST._INewtypeRange _3764___mcc_h981 = _source163.dtor_range;
                bool _3765___mcc_h982 = _source163.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3766___mcc_h983 = _source163.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3767_attributes = _3766___mcc_h983;
                bool _3768_erase = _3765___mcc_h982;
                DAST._INewtypeRange _3769_range = _3764___mcc_h981;
                DAST._IType _3770_b = _3763___mcc_h980;
                {
                  RAST._IExpr _out1056;
                  DCOMP._IOwnership _out1057;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1058;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out1056, out _out1057, out _out1058);
                  r = _out1056;
                  resultingOwnership = _out1057;
                  readIdents = _out1058;
                }
              }
            } else if (_source162.is_Nullable) {
              DAST._IType _3771___mcc_h988 = _source162.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out1059;
                DCOMP._IOwnership _out1060;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1061;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1059, out _out1060, out _out1061);
                r = _out1059;
                resultingOwnership = _out1060;
                readIdents = _out1061;
              }
            } else if (_source162.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3772___mcc_h990 = _source162.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out1062;
                DCOMP._IOwnership _out1063;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1064;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1062, out _out1063, out _out1064);
                r = _out1062;
                resultingOwnership = _out1063;
                readIdents = _out1064;
              }
            } else if (_source162.is_Array) {
              DAST._IType _3773___mcc_h992 = _source162.dtor_element;
              BigInteger _3774___mcc_h993 = _source162.dtor_dims;
              {
                RAST._IExpr _out1065;
                DCOMP._IOwnership _out1066;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1067;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1065, out _out1066, out _out1067);
                r = _out1065;
                resultingOwnership = _out1066;
                readIdents = _out1067;
              }
            } else if (_source162.is_Seq) {
              DAST._IType _3775___mcc_h996 = _source162.dtor_element;
              {
                RAST._IExpr _out1068;
                DCOMP._IOwnership _out1069;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1070;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1068, out _out1069, out _out1070);
                r = _out1068;
                resultingOwnership = _out1069;
                readIdents = _out1070;
              }
            } else if (_source162.is_Set) {
              DAST._IType _3776___mcc_h998 = _source162.dtor_element;
              {
                RAST._IExpr _out1071;
                DCOMP._IOwnership _out1072;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1073;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1071, out _out1072, out _out1073);
                r = _out1071;
                resultingOwnership = _out1072;
                readIdents = _out1073;
              }
            } else if (_source162.is_Multiset) {
              DAST._IType _3777___mcc_h1000 = _source162.dtor_element;
              {
                RAST._IExpr _out1074;
                DCOMP._IOwnership _out1075;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1076;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1074, out _out1075, out _out1076);
                r = _out1074;
                resultingOwnership = _out1075;
                readIdents = _out1076;
              }
            } else if (_source162.is_Map) {
              DAST._IType _3778___mcc_h1002 = _source162.dtor_key;
              DAST._IType _3779___mcc_h1003 = _source162.dtor_value;
              {
                RAST._IExpr _out1077;
                DCOMP._IOwnership _out1078;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1079;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1077, out _out1078, out _out1079);
                r = _out1077;
                resultingOwnership = _out1078;
                readIdents = _out1079;
              }
            } else if (_source162.is_SetBuilder) {
              DAST._IType _3780___mcc_h1006 = _source162.dtor_element;
              {
                RAST._IExpr _out1080;
                DCOMP._IOwnership _out1081;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1082;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1080, out _out1081, out _out1082);
                r = _out1080;
                resultingOwnership = _out1081;
                readIdents = _out1082;
              }
            } else if (_source162.is_MapBuilder) {
              DAST._IType _3781___mcc_h1008 = _source162.dtor_key;
              DAST._IType _3782___mcc_h1009 = _source162.dtor_value;
              {
                RAST._IExpr _out1083;
                DCOMP._IOwnership _out1084;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1085;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1083, out _out1084, out _out1085);
                r = _out1083;
                resultingOwnership = _out1084;
                readIdents = _out1085;
              }
            } else if (_source162.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3783___mcc_h1012 = _source162.dtor_args;
              DAST._IType _3784___mcc_h1013 = _source162.dtor_result;
              {
                RAST._IExpr _out1086;
                DCOMP._IOwnership _out1087;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1088;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1086, out _out1087, out _out1088);
                r = _out1086;
                resultingOwnership = _out1087;
                readIdents = _out1088;
              }
            } else if (_source162.is_Primitive) {
              DAST._IPrimitive _3785___mcc_h1016 = _source162.dtor_Primitive_i_a0;
              {
                RAST._IExpr _out1089;
                DCOMP._IOwnership _out1090;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1091;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1089, out _out1090, out _out1091);
                r = _out1089;
                resultingOwnership = _out1090;
                readIdents = _out1091;
              }
            } else if (_source162.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3786___mcc_h1018 = _source162.dtor_Passthrough_i_a0;
              {
                RAST._IExpr _out1092;
                DCOMP._IOwnership _out1093;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1094;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1092, out _out1093, out _out1094);
                r = _out1092;
                resultingOwnership = _out1093;
                readIdents = _out1094;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3787___mcc_h1020 = _source162.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out1095;
                DCOMP._IOwnership _out1096;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1097;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1095, out _out1096, out _out1097);
                r = _out1095;
                resultingOwnership = _out1096;
                readIdents = _out1097;
              }
            }
          } else if (_source155.is_Bool) {
            DAST._IType _source164 = _3200___mcc_h1;
            if (_source164.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3788___mcc_h1022 = _source164.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3789___mcc_h1023 = _source164.dtor_typeArgs;
              DAST._IResolvedType _3790___mcc_h1024 = _source164.dtor_resolved;
              DAST._IResolvedType _source165 = _3790___mcc_h1024;
              if (_source165.is_Datatype) {
                DAST._IDatatypeType _3791___mcc_h1028 = _source165.dtor_datatypeType;
                {
                  RAST._IExpr _out1098;
                  DCOMP._IOwnership _out1099;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1100;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1098, out _out1099, out _out1100);
                  r = _out1098;
                  resultingOwnership = _out1099;
                  readIdents = _out1100;
                }
              } else if (_source165.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3792___mcc_h1030 = _source165.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3793___mcc_h1031 = _source165.dtor_attributes;
                {
                  RAST._IExpr _out1101;
                  DCOMP._IOwnership _out1102;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1103;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1101, out _out1102, out _out1103);
                  r = _out1101;
                  resultingOwnership = _out1102;
                  readIdents = _out1103;
                }
              } else {
                DAST._IType _3794___mcc_h1034 = _source165.dtor_baseType;
                DAST._INewtypeRange _3795___mcc_h1035 = _source165.dtor_range;
                bool _3796___mcc_h1036 = _source165.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3797___mcc_h1037 = _source165.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3798_attributes = _3797___mcc_h1037;
                bool _3799_erase = _3796___mcc_h1036;
                DAST._INewtypeRange _3800_range = _3795___mcc_h1035;
                DAST._IType _3801_b = _3794___mcc_h1034;
                {
                  RAST._IExpr _out1104;
                  DCOMP._IOwnership _out1105;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1106;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out1104, out _out1105, out _out1106);
                  r = _out1104;
                  resultingOwnership = _out1105;
                  readIdents = _out1106;
                }
              }
            } else if (_source164.is_Nullable) {
              DAST._IType _3802___mcc_h1042 = _source164.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out1107;
                DCOMP._IOwnership _out1108;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1109;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1107, out _out1108, out _out1109);
                r = _out1107;
                resultingOwnership = _out1108;
                readIdents = _out1109;
              }
            } else if (_source164.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3803___mcc_h1044 = _source164.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out1110;
                DCOMP._IOwnership _out1111;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1112;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1110, out _out1111, out _out1112);
                r = _out1110;
                resultingOwnership = _out1111;
                readIdents = _out1112;
              }
            } else if (_source164.is_Array) {
              DAST._IType _3804___mcc_h1046 = _source164.dtor_element;
              BigInteger _3805___mcc_h1047 = _source164.dtor_dims;
              {
                RAST._IExpr _out1113;
                DCOMP._IOwnership _out1114;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1115;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1113, out _out1114, out _out1115);
                r = _out1113;
                resultingOwnership = _out1114;
                readIdents = _out1115;
              }
            } else if (_source164.is_Seq) {
              DAST._IType _3806___mcc_h1050 = _source164.dtor_element;
              {
                RAST._IExpr _out1116;
                DCOMP._IOwnership _out1117;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1118;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1116, out _out1117, out _out1118);
                r = _out1116;
                resultingOwnership = _out1117;
                readIdents = _out1118;
              }
            } else if (_source164.is_Set) {
              DAST._IType _3807___mcc_h1052 = _source164.dtor_element;
              {
                RAST._IExpr _out1119;
                DCOMP._IOwnership _out1120;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1121;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1119, out _out1120, out _out1121);
                r = _out1119;
                resultingOwnership = _out1120;
                readIdents = _out1121;
              }
            } else if (_source164.is_Multiset) {
              DAST._IType _3808___mcc_h1054 = _source164.dtor_element;
              {
                RAST._IExpr _out1122;
                DCOMP._IOwnership _out1123;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1124;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1122, out _out1123, out _out1124);
                r = _out1122;
                resultingOwnership = _out1123;
                readIdents = _out1124;
              }
            } else if (_source164.is_Map) {
              DAST._IType _3809___mcc_h1056 = _source164.dtor_key;
              DAST._IType _3810___mcc_h1057 = _source164.dtor_value;
              {
                RAST._IExpr _out1125;
                DCOMP._IOwnership _out1126;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1127;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1125, out _out1126, out _out1127);
                r = _out1125;
                resultingOwnership = _out1126;
                readIdents = _out1127;
              }
            } else if (_source164.is_SetBuilder) {
              DAST._IType _3811___mcc_h1060 = _source164.dtor_element;
              {
                RAST._IExpr _out1128;
                DCOMP._IOwnership _out1129;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1130;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1128, out _out1129, out _out1130);
                r = _out1128;
                resultingOwnership = _out1129;
                readIdents = _out1130;
              }
            } else if (_source164.is_MapBuilder) {
              DAST._IType _3812___mcc_h1062 = _source164.dtor_key;
              DAST._IType _3813___mcc_h1063 = _source164.dtor_value;
              {
                RAST._IExpr _out1131;
                DCOMP._IOwnership _out1132;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1133;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1131, out _out1132, out _out1133);
                r = _out1131;
                resultingOwnership = _out1132;
                readIdents = _out1133;
              }
            } else if (_source164.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3814___mcc_h1066 = _source164.dtor_args;
              DAST._IType _3815___mcc_h1067 = _source164.dtor_result;
              {
                RAST._IExpr _out1134;
                DCOMP._IOwnership _out1135;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1136;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1134, out _out1135, out _out1136);
                r = _out1134;
                resultingOwnership = _out1135;
                readIdents = _out1136;
              }
            } else if (_source164.is_Primitive) {
              DAST._IPrimitive _3816___mcc_h1070 = _source164.dtor_Primitive_i_a0;
              {
                RAST._IExpr _out1137;
                DCOMP._IOwnership _out1138;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1139;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1137, out _out1138, out _out1139);
                r = _out1137;
                resultingOwnership = _out1138;
                readIdents = _out1139;
              }
            } else if (_source164.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3817___mcc_h1072 = _source164.dtor_Passthrough_i_a0;
              {
                RAST._IExpr _out1140;
                DCOMP._IOwnership _out1141;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1142;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1140, out _out1141, out _out1142);
                r = _out1140;
                resultingOwnership = _out1141;
                readIdents = _out1142;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3818___mcc_h1074 = _source164.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out1143;
                DCOMP._IOwnership _out1144;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1145;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1143, out _out1144, out _out1145);
                r = _out1143;
                resultingOwnership = _out1144;
                readIdents = _out1145;
              }
            }
          } else {
            DAST._IType _source166 = _3200___mcc_h1;
            if (_source166.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3819___mcc_h1076 = _source166.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3820___mcc_h1077 = _source166.dtor_typeArgs;
              DAST._IResolvedType _3821___mcc_h1078 = _source166.dtor_resolved;
              DAST._IResolvedType _source167 = _3821___mcc_h1078;
              if (_source167.is_Datatype) {
                DAST._IDatatypeType _3822___mcc_h1082 = _source167.dtor_datatypeType;
                {
                  RAST._IExpr _out1146;
                  DCOMP._IOwnership _out1147;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1148;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1146, out _out1147, out _out1148);
                  r = _out1146;
                  resultingOwnership = _out1147;
                  readIdents = _out1148;
                }
              } else if (_source167.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3823___mcc_h1084 = _source167.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3824___mcc_h1085 = _source167.dtor_attributes;
                {
                  RAST._IExpr _out1149;
                  DCOMP._IOwnership _out1150;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1151;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1149, out _out1150, out _out1151);
                  r = _out1149;
                  resultingOwnership = _out1150;
                  readIdents = _out1151;
                }
              } else {
                DAST._IType _3825___mcc_h1088 = _source167.dtor_baseType;
                DAST._INewtypeRange _3826___mcc_h1089 = _source167.dtor_range;
                bool _3827___mcc_h1090 = _source167.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3828___mcc_h1091 = _source167.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3829_attributes = _3828___mcc_h1091;
                bool _3830_erase = _3827___mcc_h1090;
                DAST._INewtypeRange _3831_range = _3826___mcc_h1089;
                DAST._IType _3832_b = _3825___mcc_h1088;
                {
                  RAST._IExpr _out1152;
                  DCOMP._IOwnership _out1153;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1154;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out1152, out _out1153, out _out1154);
                  r = _out1152;
                  resultingOwnership = _out1153;
                  readIdents = _out1154;
                }
              }
            } else if (_source166.is_Nullable) {
              DAST._IType _3833___mcc_h1096 = _source166.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out1155;
                DCOMP._IOwnership _out1156;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1157;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1155, out _out1156, out _out1157);
                r = _out1155;
                resultingOwnership = _out1156;
                readIdents = _out1157;
              }
            } else if (_source166.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3834___mcc_h1098 = _source166.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out1158;
                DCOMP._IOwnership _out1159;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1160;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1158, out _out1159, out _out1160);
                r = _out1158;
                resultingOwnership = _out1159;
                readIdents = _out1160;
              }
            } else if (_source166.is_Array) {
              DAST._IType _3835___mcc_h1100 = _source166.dtor_element;
              BigInteger _3836___mcc_h1101 = _source166.dtor_dims;
              {
                RAST._IExpr _out1161;
                DCOMP._IOwnership _out1162;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1163;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1161, out _out1162, out _out1163);
                r = _out1161;
                resultingOwnership = _out1162;
                readIdents = _out1163;
              }
            } else if (_source166.is_Seq) {
              DAST._IType _3837___mcc_h1104 = _source166.dtor_element;
              {
                RAST._IExpr _out1164;
                DCOMP._IOwnership _out1165;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1166;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1164, out _out1165, out _out1166);
                r = _out1164;
                resultingOwnership = _out1165;
                readIdents = _out1166;
              }
            } else if (_source166.is_Set) {
              DAST._IType _3838___mcc_h1106 = _source166.dtor_element;
              {
                RAST._IExpr _out1167;
                DCOMP._IOwnership _out1168;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1169;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1167, out _out1168, out _out1169);
                r = _out1167;
                resultingOwnership = _out1168;
                readIdents = _out1169;
              }
            } else if (_source166.is_Multiset) {
              DAST._IType _3839___mcc_h1108 = _source166.dtor_element;
              {
                RAST._IExpr _out1170;
                DCOMP._IOwnership _out1171;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1172;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1170, out _out1171, out _out1172);
                r = _out1170;
                resultingOwnership = _out1171;
                readIdents = _out1172;
              }
            } else if (_source166.is_Map) {
              DAST._IType _3840___mcc_h1110 = _source166.dtor_key;
              DAST._IType _3841___mcc_h1111 = _source166.dtor_value;
              {
                RAST._IExpr _out1173;
                DCOMP._IOwnership _out1174;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1175;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1173, out _out1174, out _out1175);
                r = _out1173;
                resultingOwnership = _out1174;
                readIdents = _out1175;
              }
            } else if (_source166.is_SetBuilder) {
              DAST._IType _3842___mcc_h1114 = _source166.dtor_element;
              {
                RAST._IExpr _out1176;
                DCOMP._IOwnership _out1177;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1178;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1176, out _out1177, out _out1178);
                r = _out1176;
                resultingOwnership = _out1177;
                readIdents = _out1178;
              }
            } else if (_source166.is_MapBuilder) {
              DAST._IType _3843___mcc_h1116 = _source166.dtor_key;
              DAST._IType _3844___mcc_h1117 = _source166.dtor_value;
              {
                RAST._IExpr _out1179;
                DCOMP._IOwnership _out1180;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1181;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1179, out _out1180, out _out1181);
                r = _out1179;
                resultingOwnership = _out1180;
                readIdents = _out1181;
              }
            } else if (_source166.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3845___mcc_h1120 = _source166.dtor_args;
              DAST._IType _3846___mcc_h1121 = _source166.dtor_result;
              {
                RAST._IExpr _out1182;
                DCOMP._IOwnership _out1183;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1184;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1182, out _out1183, out _out1184);
                r = _out1182;
                resultingOwnership = _out1183;
                readIdents = _out1184;
              }
            } else if (_source166.is_Primitive) {
              DAST._IPrimitive _3847___mcc_h1124 = _source166.dtor_Primitive_i_a0;
              DAST._IPrimitive _source168 = _3847___mcc_h1124;
              if (_source168.is_Int) {
                {
                  RAST._IType _3848_rhsType;
                  RAST._IType _out1185;
                  _out1185 = (this).GenType(_3194_fromTpe, true, false);
                  _3848_rhsType = _out1185;
                  RAST._IExpr _3849_recursiveGen;
                  DCOMP._IOwnership _3850___v104;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3851_recIdents;
                  RAST._IExpr _out1186;
                  DCOMP._IOwnership _out1187;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1188;
                  (this).GenExpr(_3193_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1186, out _out1187, out _out1188);
                  _3849_recursiveGen = _out1186;
                  _3850___v104 = _out1187;
                  _3851_recIdents = _out1188;
                  r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_3849_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                  RAST._IExpr _out1189;
                  DCOMP._IOwnership _out1190;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1189, out _out1190);
                  r = _out1189;
                  resultingOwnership = _out1190;
                  readIdents = _3851_recIdents;
                }
              } else if (_source168.is_Real) {
                {
                  RAST._IExpr _out1191;
                  DCOMP._IOwnership _out1192;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1193;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1191, out _out1192, out _out1193);
                  r = _out1191;
                  resultingOwnership = _out1192;
                  readIdents = _out1193;
                }
              } else if (_source168.is_String) {
                {
                  RAST._IExpr _out1194;
                  DCOMP._IOwnership _out1195;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1196;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1194, out _out1195, out _out1196);
                  r = _out1194;
                  resultingOwnership = _out1195;
                  readIdents = _out1196;
                }
              } else if (_source168.is_Bool) {
                {
                  RAST._IExpr _out1197;
                  DCOMP._IOwnership _out1198;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1199;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1197, out _out1198, out _out1199);
                  r = _out1197;
                  resultingOwnership = _out1198;
                  readIdents = _out1199;
                }
              } else {
                {
                  RAST._IExpr _out1200;
                  DCOMP._IOwnership _out1201;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1202;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1200, out _out1201, out _out1202);
                  r = _out1200;
                  resultingOwnership = _out1201;
                  readIdents = _out1202;
                }
              }
            } else if (_source166.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3852___mcc_h1126 = _source166.dtor_Passthrough_i_a0;
              {
                RAST._IExpr _out1203;
                DCOMP._IOwnership _out1204;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1205;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1203, out _out1204, out _out1205);
                r = _out1203;
                resultingOwnership = _out1204;
                readIdents = _out1205;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3853___mcc_h1128 = _source166.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out1206;
                DCOMP._IOwnership _out1207;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1208;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1206, out _out1207, out _out1208);
                r = _out1206;
                resultingOwnership = _out1207;
                readIdents = _out1208;
              }
            }
          }
        } else if (_source127.is_Passthrough) {
          Dafny.ISequence<Dafny.Rune> _3854___mcc_h1130 = _source127.dtor_Passthrough_i_a0;
          DAST._IType _source169 = _3200___mcc_h1;
          if (_source169.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3855___mcc_h1134 = _source169.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3856___mcc_h1135 = _source169.dtor_typeArgs;
            DAST._IResolvedType _3857___mcc_h1136 = _source169.dtor_resolved;
            DAST._IResolvedType _source170 = _3857___mcc_h1136;
            if (_source170.is_Datatype) {
              DAST._IDatatypeType _3858___mcc_h1140 = _source170.dtor_datatypeType;
              {
                RAST._IExpr _out1209;
                DCOMP._IOwnership _out1210;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1211;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1209, out _out1210, out _out1211);
                r = _out1209;
                resultingOwnership = _out1210;
                readIdents = _out1211;
              }
            } else if (_source170.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3859___mcc_h1142 = _source170.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3860___mcc_h1143 = _source170.dtor_attributes;
              {
                RAST._IExpr _out1212;
                DCOMP._IOwnership _out1213;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1214;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1212, out _out1213, out _out1214);
                r = _out1212;
                resultingOwnership = _out1213;
                readIdents = _out1214;
              }
            } else {
              DAST._IType _3861___mcc_h1146 = _source170.dtor_baseType;
              DAST._INewtypeRange _3862___mcc_h1147 = _source170.dtor_range;
              bool _3863___mcc_h1148 = _source170.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3864___mcc_h1149 = _source170.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3865_attributes = _3864___mcc_h1149;
              bool _3866_erase = _3863___mcc_h1148;
              DAST._INewtypeRange _3867_range = _3862___mcc_h1147;
              DAST._IType _3868_b = _3861___mcc_h1146;
              {
                RAST._IExpr _out1215;
                DCOMP._IOwnership _out1216;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1217;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out1215, out _out1216, out _out1217);
                r = _out1215;
                resultingOwnership = _out1216;
                readIdents = _out1217;
              }
            }
          } else if (_source169.is_Nullable) {
            DAST._IType _3869___mcc_h1154 = _source169.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out1218;
              DCOMP._IOwnership _out1219;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1220;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1218, out _out1219, out _out1220);
              r = _out1218;
              resultingOwnership = _out1219;
              readIdents = _out1220;
            }
          } else if (_source169.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3870___mcc_h1156 = _source169.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out1221;
              DCOMP._IOwnership _out1222;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1223;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1221, out _out1222, out _out1223);
              r = _out1221;
              resultingOwnership = _out1222;
              readIdents = _out1223;
            }
          } else if (_source169.is_Array) {
            DAST._IType _3871___mcc_h1158 = _source169.dtor_element;
            BigInteger _3872___mcc_h1159 = _source169.dtor_dims;
            {
              RAST._IExpr _out1224;
              DCOMP._IOwnership _out1225;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1226;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1224, out _out1225, out _out1226);
              r = _out1224;
              resultingOwnership = _out1225;
              readIdents = _out1226;
            }
          } else if (_source169.is_Seq) {
            DAST._IType _3873___mcc_h1162 = _source169.dtor_element;
            {
              RAST._IExpr _out1227;
              DCOMP._IOwnership _out1228;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1229;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1227, out _out1228, out _out1229);
              r = _out1227;
              resultingOwnership = _out1228;
              readIdents = _out1229;
            }
          } else if (_source169.is_Set) {
            DAST._IType _3874___mcc_h1164 = _source169.dtor_element;
            {
              RAST._IExpr _out1230;
              DCOMP._IOwnership _out1231;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1232;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1230, out _out1231, out _out1232);
              r = _out1230;
              resultingOwnership = _out1231;
              readIdents = _out1232;
            }
          } else if (_source169.is_Multiset) {
            DAST._IType _3875___mcc_h1166 = _source169.dtor_element;
            {
              RAST._IExpr _out1233;
              DCOMP._IOwnership _out1234;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1235;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1233, out _out1234, out _out1235);
              r = _out1233;
              resultingOwnership = _out1234;
              readIdents = _out1235;
            }
          } else if (_source169.is_Map) {
            DAST._IType _3876___mcc_h1168 = _source169.dtor_key;
            DAST._IType _3877___mcc_h1169 = _source169.dtor_value;
            {
              RAST._IExpr _out1236;
              DCOMP._IOwnership _out1237;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1238;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1236, out _out1237, out _out1238);
              r = _out1236;
              resultingOwnership = _out1237;
              readIdents = _out1238;
            }
          } else if (_source169.is_SetBuilder) {
            DAST._IType _3878___mcc_h1172 = _source169.dtor_element;
            {
              RAST._IExpr _out1239;
              DCOMP._IOwnership _out1240;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1241;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1239, out _out1240, out _out1241);
              r = _out1239;
              resultingOwnership = _out1240;
              readIdents = _out1241;
            }
          } else if (_source169.is_MapBuilder) {
            DAST._IType _3879___mcc_h1174 = _source169.dtor_key;
            DAST._IType _3880___mcc_h1175 = _source169.dtor_value;
            {
              RAST._IExpr _out1242;
              DCOMP._IOwnership _out1243;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1244;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1242, out _out1243, out _out1244);
              r = _out1242;
              resultingOwnership = _out1243;
              readIdents = _out1244;
            }
          } else if (_source169.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3881___mcc_h1178 = _source169.dtor_args;
            DAST._IType _3882___mcc_h1179 = _source169.dtor_result;
            {
              RAST._IExpr _out1245;
              DCOMP._IOwnership _out1246;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1247;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1245, out _out1246, out _out1247);
              r = _out1245;
              resultingOwnership = _out1246;
              readIdents = _out1247;
            }
          } else if (_source169.is_Primitive) {
            DAST._IPrimitive _3883___mcc_h1182 = _source169.dtor_Primitive_i_a0;
            DAST._IPrimitive _source171 = _3883___mcc_h1182;
            if (_source171.is_Int) {
              {
                RAST._IType _3884_rhsType;
                RAST._IType _out1248;
                _out1248 = (this).GenType(_3194_fromTpe, true, false);
                _3884_rhsType = _out1248;
                RAST._IExpr _3885_recursiveGen;
                DCOMP._IOwnership _3886___v102;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3887_recIdents;
                RAST._IExpr _out1249;
                DCOMP._IOwnership _out1250;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1251;
                (this).GenExpr(_3193_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1249, out _out1250, out _out1251);
                _3885_recursiveGen = _out1249;
                _3886___v102 = _out1250;
                _3887_recIdents = _out1251;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::dafny_runtime::BigInt::from("), (_3885_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")}")));
                RAST._IExpr _out1252;
                DCOMP._IOwnership _out1253;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1252, out _out1253);
                r = _out1252;
                resultingOwnership = _out1253;
                readIdents = _3887_recIdents;
              }
            } else if (_source171.is_Real) {
              {
                RAST._IExpr _out1254;
                DCOMP._IOwnership _out1255;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1256;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1254, out _out1255, out _out1256);
                r = _out1254;
                resultingOwnership = _out1255;
                readIdents = _out1256;
              }
            } else if (_source171.is_String) {
              {
                RAST._IExpr _out1257;
                DCOMP._IOwnership _out1258;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1259;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1257, out _out1258, out _out1259);
                r = _out1257;
                resultingOwnership = _out1258;
                readIdents = _out1259;
              }
            } else if (_source171.is_Bool) {
              {
                RAST._IExpr _out1260;
                DCOMP._IOwnership _out1261;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1262;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1260, out _out1261, out _out1262);
                r = _out1260;
                resultingOwnership = _out1261;
                readIdents = _out1262;
              }
            } else {
              {
                RAST._IExpr _out1263;
                DCOMP._IOwnership _out1264;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1265;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1263, out _out1264, out _out1265);
                r = _out1263;
                resultingOwnership = _out1264;
                readIdents = _out1265;
              }
            }
          } else if (_source169.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3888___mcc_h1184 = _source169.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _3889_recursiveGen;
              DCOMP._IOwnership _3890___v107;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3891_recIdents;
              RAST._IExpr _out1266;
              DCOMP._IOwnership _out1267;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1268;
              (this).GenExpr(_3193_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1266, out _out1267, out _out1268);
              _3889_recursiveGen = _out1266;
              _3890___v107 = _out1267;
              _3891_recIdents = _out1268;
              RAST._IType _3892_toTpeGen;
              RAST._IType _out1269;
              _out1269 = (this).GenType(_3195_toTpe, true, false);
              _3892_toTpeGen = _out1269;
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_3889_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_3892_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
              RAST._IExpr _out1270;
              DCOMP._IOwnership _out1271;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1270, out _out1271);
              r = _out1270;
              resultingOwnership = _out1271;
              readIdents = _3891_recIdents;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3893___mcc_h1186 = _source169.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out1272;
              DCOMP._IOwnership _out1273;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1274;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1272, out _out1273, out _out1274);
              r = _out1272;
              resultingOwnership = _out1273;
              readIdents = _out1274;
            }
          }
        } else {
          Dafny.ISequence<Dafny.Rune> _3894___mcc_h1188 = _source127.dtor_TypeArg_i_a0;
          DAST._IType _source172 = _3200___mcc_h1;
          if (_source172.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3895___mcc_h1192 = _source172.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3896___mcc_h1193 = _source172.dtor_typeArgs;
            DAST._IResolvedType _3897___mcc_h1194 = _source172.dtor_resolved;
            DAST._IResolvedType _source173 = _3897___mcc_h1194;
            if (_source173.is_Datatype) {
              DAST._IDatatypeType _3898___mcc_h1198 = _source173.dtor_datatypeType;
              {
                RAST._IExpr _out1275;
                DCOMP._IOwnership _out1276;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1277;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1275, out _out1276, out _out1277);
                r = _out1275;
                resultingOwnership = _out1276;
                readIdents = _out1277;
              }
            } else if (_source173.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3899___mcc_h1200 = _source173.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3900___mcc_h1201 = _source173.dtor_attributes;
              {
                RAST._IExpr _out1278;
                DCOMP._IOwnership _out1279;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1280;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1278, out _out1279, out _out1280);
                r = _out1278;
                resultingOwnership = _out1279;
                readIdents = _out1280;
              }
            } else {
              DAST._IType _3901___mcc_h1204 = _source173.dtor_baseType;
              DAST._INewtypeRange _3902___mcc_h1205 = _source173.dtor_range;
              bool _3903___mcc_h1206 = _source173.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3904___mcc_h1207 = _source173.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3905_attributes = _3904___mcc_h1207;
              bool _3906_erase = _3903___mcc_h1206;
              DAST._INewtypeRange _3907_range = _3902___mcc_h1205;
              DAST._IType _3908_b = _3901___mcc_h1204;
              {
                RAST._IExpr _out1281;
                DCOMP._IOwnership _out1282;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1283;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out1281, out _out1282, out _out1283);
                r = _out1281;
                resultingOwnership = _out1282;
                readIdents = _out1283;
              }
            }
          } else if (_source172.is_Nullable) {
            DAST._IType _3909___mcc_h1212 = _source172.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out1284;
              DCOMP._IOwnership _out1285;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1286;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1284, out _out1285, out _out1286);
              r = _out1284;
              resultingOwnership = _out1285;
              readIdents = _out1286;
            }
          } else if (_source172.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3910___mcc_h1214 = _source172.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out1287;
              DCOMP._IOwnership _out1288;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1289;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1287, out _out1288, out _out1289);
              r = _out1287;
              resultingOwnership = _out1288;
              readIdents = _out1289;
            }
          } else if (_source172.is_Array) {
            DAST._IType _3911___mcc_h1216 = _source172.dtor_element;
            BigInteger _3912___mcc_h1217 = _source172.dtor_dims;
            {
              RAST._IExpr _out1290;
              DCOMP._IOwnership _out1291;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1292;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1290, out _out1291, out _out1292);
              r = _out1290;
              resultingOwnership = _out1291;
              readIdents = _out1292;
            }
          } else if (_source172.is_Seq) {
            DAST._IType _3913___mcc_h1220 = _source172.dtor_element;
            {
              RAST._IExpr _out1293;
              DCOMP._IOwnership _out1294;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1295;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1293, out _out1294, out _out1295);
              r = _out1293;
              resultingOwnership = _out1294;
              readIdents = _out1295;
            }
          } else if (_source172.is_Set) {
            DAST._IType _3914___mcc_h1222 = _source172.dtor_element;
            {
              RAST._IExpr _out1296;
              DCOMP._IOwnership _out1297;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1298;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1296, out _out1297, out _out1298);
              r = _out1296;
              resultingOwnership = _out1297;
              readIdents = _out1298;
            }
          } else if (_source172.is_Multiset) {
            DAST._IType _3915___mcc_h1224 = _source172.dtor_element;
            {
              RAST._IExpr _out1299;
              DCOMP._IOwnership _out1300;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1301;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1299, out _out1300, out _out1301);
              r = _out1299;
              resultingOwnership = _out1300;
              readIdents = _out1301;
            }
          } else if (_source172.is_Map) {
            DAST._IType _3916___mcc_h1226 = _source172.dtor_key;
            DAST._IType _3917___mcc_h1227 = _source172.dtor_value;
            {
              RAST._IExpr _out1302;
              DCOMP._IOwnership _out1303;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1304;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1302, out _out1303, out _out1304);
              r = _out1302;
              resultingOwnership = _out1303;
              readIdents = _out1304;
            }
          } else if (_source172.is_SetBuilder) {
            DAST._IType _3918___mcc_h1230 = _source172.dtor_element;
            {
              RAST._IExpr _out1305;
              DCOMP._IOwnership _out1306;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1307;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1305, out _out1306, out _out1307);
              r = _out1305;
              resultingOwnership = _out1306;
              readIdents = _out1307;
            }
          } else if (_source172.is_MapBuilder) {
            DAST._IType _3919___mcc_h1232 = _source172.dtor_key;
            DAST._IType _3920___mcc_h1233 = _source172.dtor_value;
            {
              RAST._IExpr _out1308;
              DCOMP._IOwnership _out1309;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1310;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1308, out _out1309, out _out1310);
              r = _out1308;
              resultingOwnership = _out1309;
              readIdents = _out1310;
            }
          } else if (_source172.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3921___mcc_h1236 = _source172.dtor_args;
            DAST._IType _3922___mcc_h1237 = _source172.dtor_result;
            {
              RAST._IExpr _out1311;
              DCOMP._IOwnership _out1312;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1313;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1311, out _out1312, out _out1313);
              r = _out1311;
              resultingOwnership = _out1312;
              readIdents = _out1313;
            }
          } else if (_source172.is_Primitive) {
            DAST._IPrimitive _3923___mcc_h1240 = _source172.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out1314;
              DCOMP._IOwnership _out1315;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1316;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1314, out _out1315, out _out1316);
              r = _out1314;
              resultingOwnership = _out1315;
              readIdents = _out1316;
            }
          } else if (_source172.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3924___mcc_h1242 = _source172.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out1317;
              DCOMP._IOwnership _out1318;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1319;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1317, out _out1318, out _out1319);
              r = _out1317;
              resultingOwnership = _out1318;
              readIdents = _out1319;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3925___mcc_h1244 = _source172.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out1320;
              DCOMP._IOwnership _out1321;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1322;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1320, out _out1321, out _out1322);
              r = _out1320;
              resultingOwnership = _out1321;
              readIdents = _out1322;
            }
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
      Std.Wrappers._IOption<RAST._IType> _3926_tpe;
      _3926_tpe = (env).GetType(rName);
      bool _3927_currentlyBorrowed;
      _3927_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _3928_noNeedOfClone;
      _3928_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        r = RAST.__default.BorrowMut(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        if (!(_3928_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_3928_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_3927_currentlyBorrowed) {
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
      DAST._IExpression _source174 = e;
      if (_source174.is_Literal) {
        DAST._ILiteral _3929___mcc_h0 = _source174.dtor_Literal_i_a0;
        RAST._IExpr _out1323;
        DCOMP._IOwnership _out1324;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1325;
        (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out1323, out _out1324, out _out1325);
        r = _out1323;
        resultingOwnership = _out1324;
        readIdents = _out1325;
      } else if (_source174.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _3930___mcc_h1 = _source174.dtor_Ident_i_a0;
        Dafny.ISequence<Dafny.Rune> _3931_name = _3930___mcc_h1;
        {
          RAST._IExpr _out1326;
          DCOMP._IOwnership _out1327;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1328;
          (this).GenIdent(DCOMP.__default.escapeName(_3931_name), selfIdent, env, expectedOwnership, out _out1326, out _out1327, out _out1328);
          r = _out1326;
          resultingOwnership = _out1327;
          readIdents = _out1328;
        }
      } else if (_source174.is_Companion) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3932___mcc_h2 = _source174.dtor_Companion_i_a0;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3933_path = _3932___mcc_h2;
        {
          RAST._IExpr _out1329;
          _out1329 = DCOMP.COMP.GenPathExpr(_3933_path);
          r = _out1329;
          if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
            resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
          } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
            resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
          } else {
            RAST._IExpr _out1330;
            DCOMP._IOwnership _out1331;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1330, out _out1331);
            r = _out1330;
            resultingOwnership = _out1331;
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source174.is_Tuple) {
        Dafny.ISequence<DAST._IExpression> _3934___mcc_h3 = _source174.dtor_Tuple_i_a0;
        Dafny.ISequence<DAST._IExpression> _3935_values = _3934___mcc_h3;
        {
          Dafny.ISequence<RAST._IExpr> _3936_exprs;
          _3936_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _hi30 = new BigInteger((_3935_values).Count);
          for (BigInteger _3937_i = BigInteger.Zero; _3937_i < _hi30; _3937_i++) {
            RAST._IExpr _3938_recursiveGen;
            DCOMP._IOwnership _3939___v110;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3940_recIdents;
            RAST._IExpr _out1332;
            DCOMP._IOwnership _out1333;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1334;
            (this).GenExpr((_3935_values).Select(_3937_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1332, out _out1333, out _out1334);
            _3938_recursiveGen = _out1332;
            _3939___v110 = _out1333;
            _3940_recIdents = _out1334;
            _3936_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_3936_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_3938_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3940_recIdents);
          }
          r = RAST.Expr.create_Tuple(_3936_exprs);
          RAST._IExpr _out1335;
          DCOMP._IOwnership _out1336;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1335, out _out1336);
          r = _out1335;
          resultingOwnership = _out1336;
          return ;
        }
      } else if (_source174.is_New) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3941___mcc_h4 = _source174.dtor_path;
        Dafny.ISequence<DAST._IType> _3942___mcc_h5 = _source174.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _3943___mcc_h6 = _source174.dtor_args;
        Dafny.ISequence<DAST._IExpression> _3944_args = _3943___mcc_h6;
        Dafny.ISequence<DAST._IType> _3945_typeArgs = _3942___mcc_h5;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3946_path = _3941___mcc_h4;
        {
          RAST._IExpr _out1337;
          _out1337 = DCOMP.COMP.GenPathExpr(_3946_path);
          r = _out1337;
          if ((new BigInteger((_3945_typeArgs).Count)).Sign == 1) {
            Dafny.ISequence<RAST._IType> _3947_typeExprs;
            _3947_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi31 = new BigInteger((_3945_typeArgs).Count);
            for (BigInteger _3948_i = BigInteger.Zero; _3948_i < _hi31; _3948_i++) {
              RAST._IType _3949_typeExpr;
              RAST._IType _out1338;
              _out1338 = (this).GenType((_3945_typeArgs).Select(_3948_i), false, false);
              _3949_typeExpr = _out1338;
              _3947_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_3947_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_3949_typeExpr));
            }
            r = (r).ApplyType(_3947_typeExprs);
          }
          r = (r).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_allocated"));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<RAST._IExpr> _3950_arguments;
          _3950_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi32 = new BigInteger((_3944_args).Count);
          for (BigInteger _3951_i = BigInteger.Zero; _3951_i < _hi32; _3951_i++) {
            RAST._IExpr _3952_recursiveGen;
            DCOMP._IOwnership _3953___v111;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3954_recIdents;
            RAST._IExpr _out1339;
            DCOMP._IOwnership _out1340;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1341;
            (this).GenExpr((_3944_args).Select(_3951_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1339, out _out1340, out _out1341);
            _3952_recursiveGen = _out1339;
            _3953___v111 = _out1340;
            _3954_recIdents = _out1341;
            _3950_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_3950_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_3952_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3954_recIdents);
          }
          r = (r).Apply(_3950_arguments);
          RAST._IExpr _out1342;
          DCOMP._IOwnership _out1343;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1342, out _out1343);
          r = _out1342;
          resultingOwnership = _out1343;
          return ;
        }
      } else if (_source174.is_NewArray) {
        Dafny.ISequence<DAST._IExpression> _3955___mcc_h7 = _source174.dtor_dims;
        DAST._IType _3956___mcc_h8 = _source174.dtor_typ;
        DAST._IType _3957_typ = _3956___mcc_h8;
        Dafny.ISequence<DAST._IExpression> _3958_dims = _3955___mcc_h7;
        {
          BigInteger _3959_i;
          _3959_i = (new BigInteger((_3958_dims).Count)) - (BigInteger.One);
          RAST._IType _3960_genTyp;
          RAST._IType _out1344;
          _out1344 = (this).GenType(_3957_typ, false, false);
          _3960_genTyp = _out1344;
          Dafny.ISequence<Dafny.Rune> _3961_s;
          _3961_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_3960_genTyp)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::std::default::Default>::default()"));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          while ((_3959_i).Sign != -1) {
            RAST._IExpr _3962_recursiveGen;
            DCOMP._IOwnership _3963___v112;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3964_recIdents;
            RAST._IExpr _out1345;
            DCOMP._IOwnership _out1346;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1347;
            (this).GenExpr((_3958_dims).Select(_3959_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1345, out _out1346, out _out1347);
            _3962_recursiveGen = _out1345;
            _3963___v112 = _out1346;
            _3964_recIdents = _out1347;
            _3961_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), _3961_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), (_3962_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3964_recIdents);
            _3959_i = (_3959_i) - (BigInteger.One);
          }
          r = RAST.Expr.create_RawExpr(_3961_s);
          RAST._IExpr _out1348;
          DCOMP._IOwnership _out1349;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1348, out _out1349);
          r = _out1348;
          resultingOwnership = _out1349;
        }
      } else if (_source174.is_DatatypeValue) {
        DAST._IDatatypeType _3965___mcc_h9 = _source174.dtor_datatypeType;
        Dafny.ISequence<DAST._IType> _3966___mcc_h10 = _source174.dtor_typeArgs;
        Dafny.ISequence<Dafny.Rune> _3967___mcc_h11 = _source174.dtor_variant;
        bool _3968___mcc_h12 = _source174.dtor_isCo;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _3969___mcc_h13 = _source174.dtor_contents;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _3970_values = _3969___mcc_h13;
        bool _3971_isCo = _3968___mcc_h12;
        Dafny.ISequence<Dafny.Rune> _3972_variant = _3967___mcc_h11;
        Dafny.ISequence<DAST._IType> _3973_typeArgs = _3966___mcc_h10;
        DAST._IDatatypeType _3974_datatypeType = _3965___mcc_h9;
        {
          RAST._IExpr _out1350;
          _out1350 = DCOMP.COMP.GenPathExpr((_3974_datatypeType).dtor_path);
          r = _out1350;
          Dafny.ISequence<RAST._IType> _3975_genTypeArgs;
          _3975_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _hi33 = new BigInteger((_3973_typeArgs).Count);
          for (BigInteger _3976_i = BigInteger.Zero; _3976_i < _hi33; _3976_i++) {
            RAST._IType _3977_typeExpr;
            RAST._IType _out1351;
            _out1351 = (this).GenType((_3973_typeArgs).Select(_3976_i), false, false);
            _3977_typeExpr = _out1351;
            _3975_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_3975_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_3977_typeExpr));
          }
          if ((new BigInteger((_3973_typeArgs).Count)).Sign == 1) {
            r = (r).ApplyType(_3975_genTypeArgs);
          }
          r = (r).MSel(DCOMP.__default.escapeName(_3972_variant));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<RAST._IAssignIdentifier> _3978_assignments;
          _3978_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
          BigInteger _hi34 = new BigInteger((_3970_values).Count);
          for (BigInteger _3979_i = BigInteger.Zero; _3979_i < _hi34; _3979_i++) {
            _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs63 = (_3970_values).Select(_3979_i);
            Dafny.ISequence<Dafny.Rune> _3980_name = _let_tmp_rhs63.dtor__0;
            DAST._IExpression _3981_value = _let_tmp_rhs63.dtor__1;
            if (_3971_isCo) {
              RAST._IExpr _3982_recursiveGen;
              DCOMP._IOwnership _3983___v113;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3984_recIdents;
              RAST._IExpr _out1352;
              DCOMP._IOwnership _out1353;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1354;
              (this).GenExpr(_3981_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out1352, out _out1353, out _out1354);
              _3982_recursiveGen = _out1352;
              _3983___v113 = _out1353;
              _3984_recIdents = _out1354;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3984_recIdents);
              Dafny.ISequence<Dafny.Rune> _3985_allReadCloned;
              _3985_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              while (!(_3984_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                Dafny.ISequence<Dafny.Rune> _3986_next;
                foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_3984_recIdents).Elements) {
                  _3986_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                  if ((_3984_recIdents).Contains(_3986_next)) {
                    goto after__ASSIGN_SUCH_THAT_2;
                  }
                }
                throw new System.Exception("assign-such-that search produced no value (line 3223)");
              after__ASSIGN_SUCH_THAT_2: ;
                _3985_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3985_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _3986_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _3986_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                _3984_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_3984_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_3986_next));
              }
              Dafny.ISequence<Dafny.Rune> _3987_wasAssigned;
              _3987_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _3985_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_3982_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
              _3978_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_3978_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_3980_name, RAST.Expr.create_RawExpr(_3987_wasAssigned))));
            } else {
              RAST._IExpr _3988_recursiveGen;
              DCOMP._IOwnership _3989___v114;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3990_recIdents;
              RAST._IExpr _out1355;
              DCOMP._IOwnership _out1356;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1357;
              (this).GenExpr(_3981_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1355, out _out1356, out _out1357);
              _3988_recursiveGen = _out1355;
              _3989___v114 = _out1356;
              _3990_recIdents = _out1357;
              _3978_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_3978_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_3980_name, _3988_recursiveGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3990_recIdents);
            }
          }
          r = RAST.Expr.create_StructBuild(r, _3978_assignments);
          r = RAST.__default.RcNew(r);
          RAST._IExpr _out1358;
          DCOMP._IOwnership _out1359;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1358, out _out1359);
          r = _out1358;
          resultingOwnership = _out1359;
          return ;
        }
      } else if (_source174.is_Convert) {
        DAST._IExpression _3991___mcc_h14 = _source174.dtor_value;
        DAST._IType _3992___mcc_h15 = _source174.dtor_from;
        DAST._IType _3993___mcc_h16 = _source174.dtor_typ;
        {
          RAST._IExpr _out1360;
          DCOMP._IOwnership _out1361;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1362;
          (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out1360, out _out1361, out _out1362);
          r = _out1360;
          resultingOwnership = _out1361;
          readIdents = _out1362;
        }
      } else if (_source174.is_SeqConstruct) {
        DAST._IExpression _3994___mcc_h17 = _source174.dtor_length;
        DAST._IExpression _3995___mcc_h18 = _source174.dtor_elem;
        DAST._IExpression _3996_expr = _3995___mcc_h18;
        DAST._IExpression _3997_length = _3994___mcc_h17;
        {
          RAST._IExpr _3998_recursiveGen;
          DCOMP._IOwnership _3999___v118;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4000_recIdents;
          RAST._IExpr _out1363;
          DCOMP._IOwnership _out1364;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1365;
          (this).GenExpr(_3996_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1363, out _out1364, out _out1365);
          _3998_recursiveGen = _out1363;
          _3999___v118 = _out1364;
          _4000_recIdents = _out1365;
          RAST._IExpr _4001_lengthGen;
          DCOMP._IOwnership _4002___v119;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4003_lengthIdents;
          RAST._IExpr _out1366;
          DCOMP._IOwnership _out1367;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1368;
          (this).GenExpr(_3997_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1366, out _out1367, out _out1368);
          _4001_lengthGen = _out1366;
          _4002___v119 = _out1367;
          _4003_lengthIdents = _out1368;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_3998_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_4001_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4000_recIdents, _4003_lengthIdents);
          RAST._IExpr _out1369;
          DCOMP._IOwnership _out1370;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1369, out _out1370);
          r = _out1369;
          resultingOwnership = _out1370;
          return ;
        }
      } else if (_source174.is_SeqValue) {
        Dafny.ISequence<DAST._IExpression> _4004___mcc_h19 = _source174.dtor_elements;
        DAST._IType _4005___mcc_h20 = _source174.dtor_typ;
        DAST._IType _4006_typ = _4005___mcc_h20;
        Dafny.ISequence<DAST._IExpression> _4007_exprs = _4004___mcc_h19;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          RAST._IType _4008_genTpe;
          RAST._IType _out1371;
          _out1371 = (this).GenType(_4006_typ, false, false);
          _4008_genTpe = _out1371;
          BigInteger _4009_i;
          _4009_i = BigInteger.Zero;
          Dafny.ISequence<RAST._IExpr> _4010_args;
          _4010_args = Dafny.Sequence<RAST._IExpr>.FromElements();
          while ((_4009_i) < (new BigInteger((_4007_exprs).Count))) {
            RAST._IExpr _4011_recursiveGen;
            DCOMP._IOwnership _4012___v120;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4013_recIdents;
            RAST._IExpr _out1372;
            DCOMP._IOwnership _out1373;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1374;
            (this).GenExpr((_4007_exprs).Select(_4009_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1372, out _out1373, out _out1374);
            _4011_recursiveGen = _out1372;
            _4012___v120 = _out1373;
            _4013_recIdents = _out1374;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4013_recIdents);
            _4010_args = Dafny.Sequence<RAST._IExpr>.Concat(_4010_args, Dafny.Sequence<RAST._IExpr>.FromElements(_4011_recursiveGen));
            _4009_i = (_4009_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_4010_args);
          if ((new BigInteger((_4010_args).Count)).Sign == 0) {
            r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_4008_genTpe));
          }
          RAST._IExpr _out1375;
          DCOMP._IOwnership _out1376;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1375, out _out1376);
          r = _out1375;
          resultingOwnership = _out1376;
          return ;
        }
      } else if (_source174.is_SetValue) {
        Dafny.ISequence<DAST._IExpression> _4014___mcc_h21 = _source174.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _4015_exprs = _4014___mcc_h21;
        {
          Dafny.ISequence<RAST._IExpr> _4016_generatedValues;
          _4016_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _4017_i;
          _4017_i = BigInteger.Zero;
          while ((_4017_i) < (new BigInteger((_4015_exprs).Count))) {
            RAST._IExpr _4018_recursiveGen;
            DCOMP._IOwnership _4019___v121;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4020_recIdents;
            RAST._IExpr _out1377;
            DCOMP._IOwnership _out1378;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1379;
            (this).GenExpr((_4015_exprs).Select(_4017_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1377, out _out1378, out _out1379);
            _4018_recursiveGen = _out1377;
            _4019___v121 = _out1378;
            _4020_recIdents = _out1379;
            _4016_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_4016_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_4018_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4020_recIdents);
            _4017_i = (_4017_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_4016_generatedValues);
          RAST._IExpr _out1380;
          DCOMP._IOwnership _out1381;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1380, out _out1381);
          r = _out1380;
          resultingOwnership = _out1381;
          return ;
        }
      } else if (_source174.is_MultisetValue) {
        Dafny.ISequence<DAST._IExpression> _4021___mcc_h22 = _source174.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _4022_exprs = _4021___mcc_h22;
        {
          Dafny.ISequence<RAST._IExpr> _4023_generatedValues;
          _4023_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _4024_i;
          _4024_i = BigInteger.Zero;
          while ((_4024_i) < (new BigInteger((_4022_exprs).Count))) {
            RAST._IExpr _4025_recursiveGen;
            DCOMP._IOwnership _4026___v122;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4027_recIdents;
            RAST._IExpr _out1382;
            DCOMP._IOwnership _out1383;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1384;
            (this).GenExpr((_4022_exprs).Select(_4024_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1382, out _out1383, out _out1384);
            _4025_recursiveGen = _out1382;
            _4026___v122 = _out1383;
            _4027_recIdents = _out1384;
            _4023_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_4023_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_4025_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4027_recIdents);
            _4024_i = (_4024_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_4023_generatedValues);
          RAST._IExpr _out1385;
          DCOMP._IOwnership _out1386;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1385, out _out1386);
          r = _out1385;
          resultingOwnership = _out1386;
          return ;
        }
      } else if (_source174.is_MapValue) {
        Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _4028___mcc_h23 = _source174.dtor_mapElems;
        Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _4029_mapElems = _4028___mcc_h23;
        {
          Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _4030_generatedValues;
          _4030_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _4031_i;
          _4031_i = BigInteger.Zero;
          while ((_4031_i) < (new BigInteger((_4029_mapElems).Count))) {
            RAST._IExpr _4032_recursiveGenKey;
            DCOMP._IOwnership _4033___v124;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4034_recIdentsKey;
            RAST._IExpr _out1387;
            DCOMP._IOwnership _out1388;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1389;
            (this).GenExpr(((_4029_mapElems).Select(_4031_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1387, out _out1388, out _out1389);
            _4032_recursiveGenKey = _out1387;
            _4033___v124 = _out1388;
            _4034_recIdentsKey = _out1389;
            RAST._IExpr _4035_recursiveGenValue;
            DCOMP._IOwnership _4036___v125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4037_recIdentsValue;
            RAST._IExpr _out1390;
            DCOMP._IOwnership _out1391;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1392;
            (this).GenExpr(((_4029_mapElems).Select(_4031_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1390, out _out1391, out _out1392);
            _4035_recursiveGenValue = _out1390;
            _4036___v125 = _out1391;
            _4037_recIdentsValue = _out1392;
            _4030_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_4030_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_4032_recursiveGenKey, _4035_recursiveGenValue)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4034_recIdentsKey), _4037_recIdentsValue);
            _4031_i = (_4031_i) + (BigInteger.One);
          }
          _4031_i = BigInteger.Zero;
          Dafny.ISequence<RAST._IExpr> _4038_arguments;
          _4038_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          while ((_4031_i) < (new BigInteger((_4030_generatedValues).Count))) {
            RAST._IExpr _4039_genKey;
            _4039_genKey = ((_4030_generatedValues).Select(_4031_i)).dtor__0;
            RAST._IExpr _4040_genValue;
            _4040_genValue = ((_4030_generatedValues).Select(_4031_i)).dtor__1;
            _4038_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_4038_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _4039_genKey, _4040_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
            _4031_i = (_4031_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_4038_arguments);
          RAST._IExpr _out1393;
          DCOMP._IOwnership _out1394;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1393, out _out1394);
          r = _out1393;
          resultingOwnership = _out1394;
          return ;
        }
      } else if (_source174.is_MapBuilder) {
        DAST._IType _4041___mcc_h24 = _source174.dtor_keyType;
        DAST._IType _4042___mcc_h25 = _source174.dtor_valueType;
        DAST._IType _4043_valueType = _4042___mcc_h25;
        DAST._IType _4044_keyType = _4041___mcc_h24;
        {
          RAST._IType _4045_kType;
          RAST._IType _out1395;
          _out1395 = (this).GenType(_4044_keyType, false, false);
          _4045_kType = _out1395;
          RAST._IType _4046_vType;
          RAST._IType _out1396;
          _out1396 = (this).GenType(_4043_valueType, false, false);
          _4046_vType = _out1396;
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_4045_kType, _4046_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1397;
          DCOMP._IOwnership _out1398;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1397, out _out1398);
          r = _out1397;
          resultingOwnership = _out1398;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source174.is_SeqUpdate) {
        DAST._IExpression _4047___mcc_h26 = _source174.dtor_expr;
        DAST._IExpression _4048___mcc_h27 = _source174.dtor_indexExpr;
        DAST._IExpression _4049___mcc_h28 = _source174.dtor_value;
        DAST._IExpression _4050_value = _4049___mcc_h28;
        DAST._IExpression _4051_index = _4048___mcc_h27;
        DAST._IExpression _4052_expr = _4047___mcc_h26;
        {
          RAST._IExpr _4053_exprR;
          DCOMP._IOwnership _4054___v126;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4055_exprIdents;
          RAST._IExpr _out1399;
          DCOMP._IOwnership _out1400;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1401;
          (this).GenExpr(_4052_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1399, out _out1400, out _out1401);
          _4053_exprR = _out1399;
          _4054___v126 = _out1400;
          _4055_exprIdents = _out1401;
          RAST._IExpr _4056_indexR;
          DCOMP._IOwnership _4057_indexOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4058_indexIdents;
          RAST._IExpr _out1402;
          DCOMP._IOwnership _out1403;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1404;
          (this).GenExpr(_4051_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1402, out _out1403, out _out1404);
          _4056_indexR = _out1402;
          _4057_indexOwnership = _out1403;
          _4058_indexIdents = _out1404;
          RAST._IExpr _4059_valueR;
          DCOMP._IOwnership _4060_valueOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4061_valueIdents;
          RAST._IExpr _out1405;
          DCOMP._IOwnership _out1406;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1407;
          (this).GenExpr(_4050_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1405, out _out1406, out _out1407);
          _4059_valueR = _out1405;
          _4060_valueOwnership = _out1406;
          _4061_valueIdents = _out1407;
          r = ((_4053_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_4056_indexR, _4059_valueR));
          RAST._IExpr _out1408;
          DCOMP._IOwnership _out1409;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1408, out _out1409);
          r = _out1408;
          resultingOwnership = _out1409;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4055_exprIdents, _4058_indexIdents), _4061_valueIdents);
          return ;
        }
      } else if (_source174.is_MapUpdate) {
        DAST._IExpression _4062___mcc_h29 = _source174.dtor_expr;
        DAST._IExpression _4063___mcc_h30 = _source174.dtor_indexExpr;
        DAST._IExpression _4064___mcc_h31 = _source174.dtor_value;
        DAST._IExpression _4065_value = _4064___mcc_h31;
        DAST._IExpression _4066_index = _4063___mcc_h30;
        DAST._IExpression _4067_expr = _4062___mcc_h29;
        {
          RAST._IExpr _4068_exprR;
          DCOMP._IOwnership _4069___v127;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4070_exprIdents;
          RAST._IExpr _out1410;
          DCOMP._IOwnership _out1411;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1412;
          (this).GenExpr(_4067_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1410, out _out1411, out _out1412);
          _4068_exprR = _out1410;
          _4069___v127 = _out1411;
          _4070_exprIdents = _out1412;
          RAST._IExpr _4071_indexR;
          DCOMP._IOwnership _4072_indexOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4073_indexIdents;
          RAST._IExpr _out1413;
          DCOMP._IOwnership _out1414;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1415;
          (this).GenExpr(_4066_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1413, out _out1414, out _out1415);
          _4071_indexR = _out1413;
          _4072_indexOwnership = _out1414;
          _4073_indexIdents = _out1415;
          RAST._IExpr _4074_valueR;
          DCOMP._IOwnership _4075_valueOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4076_valueIdents;
          RAST._IExpr _out1416;
          DCOMP._IOwnership _out1417;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1418;
          (this).GenExpr(_4065_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1416, out _out1417, out _out1418);
          _4074_valueR = _out1416;
          _4075_valueOwnership = _out1417;
          _4076_valueIdents = _out1418;
          r = ((_4068_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_4071_indexR, _4074_valueR));
          RAST._IExpr _out1419;
          DCOMP._IOwnership _out1420;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1419, out _out1420);
          r = _out1419;
          resultingOwnership = _out1420;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4070_exprIdents, _4073_indexIdents), _4076_valueIdents);
          return ;
        }
      } else if (_source174.is_SetBuilder) {
        DAST._IType _4077___mcc_h32 = _source174.dtor_elemType;
        DAST._IType _4078_elemType = _4077___mcc_h32;
        {
          RAST._IType _4079_eType;
          RAST._IType _out1421;
          _out1421 = (this).GenType(_4078_elemType, false, false);
          _4079_eType = _out1421;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_4079_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1422;
          DCOMP._IOwnership _out1423;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1422, out _out1423);
          r = _out1422;
          resultingOwnership = _out1423;
          return ;
        }
      } else if (_source174.is_ToMultiset) {
        DAST._IExpression _4080___mcc_h33 = _source174.dtor_ToMultiset_i_a0;
        DAST._IExpression _4081_expr = _4080___mcc_h33;
        {
          RAST._IExpr _4082_recursiveGen;
          DCOMP._IOwnership _4083___v123;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4084_recIdents;
          RAST._IExpr _out1424;
          DCOMP._IOwnership _out1425;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1426;
          (this).GenExpr(_4081_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1424, out _out1425, out _out1426);
          _4082_recursiveGen = _out1424;
          _4083___v123 = _out1425;
          _4084_recIdents = _out1426;
          r = ((_4082_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          readIdents = _4084_recIdents;
          RAST._IExpr _out1427;
          DCOMP._IOwnership _out1428;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1427, out _out1428);
          r = _out1427;
          resultingOwnership = _out1428;
          return ;
        }
      } else if (_source174.is_This) {
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source175 = selfIdent;
          if (_source175.is_None) {
            {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")"));
              RAST._IExpr _out1429;
              DCOMP._IOwnership _out1430;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1429, out _out1430);
              r = _out1429;
              resultingOwnership = _out1430;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _4085___mcc_h279 = _source175.dtor_value;
            Dafny.ISequence<Dafny.Rune> _4086_id = _4085___mcc_h279;
            {
              r = RAST.Expr.create_Identifier(_4086_id);
              if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
                r = RAST.__default.Clone(r);
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
                r = RAST.__default.BoxNew(RAST.__default.Clone(r));
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
              } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
                if (!(_4086_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  r = RAST.__default.Borrow(r);
                }
                resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              } else {
                if (!(_4086_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  r = RAST.__default.BorrowMut(r);
                }
                resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
              }
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_4086_id);
            }
          }
          return ;
        }
      } else if (_source174.is_Ite) {
        DAST._IExpression _4087___mcc_h34 = _source174.dtor_cond;
        DAST._IExpression _4088___mcc_h35 = _source174.dtor_thn;
        DAST._IExpression _4089___mcc_h36 = _source174.dtor_els;
        DAST._IExpression _4090_f = _4089___mcc_h36;
        DAST._IExpression _4091_t = _4088___mcc_h35;
        DAST._IExpression _4092_cond = _4087___mcc_h34;
        {
          RAST._IExpr _4093_cond;
          DCOMP._IOwnership _4094___v128;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4095_recIdentsCond;
          RAST._IExpr _out1431;
          DCOMP._IOwnership _out1432;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1433;
          (this).GenExpr(_4092_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1431, out _out1432, out _out1433);
          _4093_cond = _out1431;
          _4094___v128 = _out1432;
          _4095_recIdentsCond = _out1433;
          Dafny.ISequence<Dafny.Rune> _4096_condString;
          _4096_condString = (_4093_cond)._ToString(DCOMP.__default.IND);
          RAST._IExpr _4097___v129;
          DCOMP._IOwnership _4098_tHasToBeOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4099___v130;
          RAST._IExpr _out1434;
          DCOMP._IOwnership _out1435;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1436;
          (this).GenExpr(_4091_t, selfIdent, env, expectedOwnership, out _out1434, out _out1435, out _out1436);
          _4097___v129 = _out1434;
          _4098_tHasToBeOwned = _out1435;
          _4099___v130 = _out1436;
          RAST._IExpr _4100_fExpr;
          DCOMP._IOwnership _4101_fOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4102_recIdentsF;
          RAST._IExpr _out1437;
          DCOMP._IOwnership _out1438;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1439;
          (this).GenExpr(_4090_f, selfIdent, env, _4098_tHasToBeOwned, out _out1437, out _out1438, out _out1439);
          _4100_fExpr = _out1437;
          _4101_fOwned = _out1438;
          _4102_recIdentsF = _out1439;
          Dafny.ISequence<Dafny.Rune> _4103_fString;
          _4103_fString = (_4100_fExpr)._ToString(DCOMP.__default.IND);
          RAST._IExpr _4104_tExpr;
          DCOMP._IOwnership _4105___v131;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4106_recIdentsT;
          RAST._IExpr _out1440;
          DCOMP._IOwnership _out1441;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1442;
          (this).GenExpr(_4091_t, selfIdent, env, _4101_fOwned, out _out1440, out _out1441, out _out1442);
          _4104_tExpr = _out1440;
          _4105___v131 = _out1441;
          _4106_recIdentsT = _out1442;
          Dafny.ISequence<Dafny.Rune> _4107_tString;
          _4107_tString = (_4104_tExpr)._ToString(DCOMP.__default.IND);
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _4096_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _4107_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _4103_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})")));
          RAST._IExpr _out1443;
          DCOMP._IOwnership _out1444;
          DCOMP.COMP.FromOwnership(r, _4101_fOwned, expectedOwnership, out _out1443, out _out1444);
          r = _out1443;
          resultingOwnership = _out1444;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4095_recIdentsCond, _4106_recIdentsT), _4102_recIdentsF);
          return ;
        }
      } else if (_source174.is_UnOp) {
        DAST._IUnaryOp _4108___mcc_h37 = _source174.dtor_unOp;
        DAST._IExpression _4109___mcc_h38 = _source174.dtor_expr;
        DAST.Format._IUnaryOpFormat _4110___mcc_h39 = _source174.dtor_format1;
        DAST._IUnaryOp _source176 = _4108___mcc_h37;
        if (_source176.is_Not) {
          DAST.Format._IUnaryOpFormat _4111_format = _4110___mcc_h39;
          DAST._IExpression _4112_e = _4109___mcc_h38;
          {
            RAST._IExpr _4113_recursiveGen;
            DCOMP._IOwnership _4114___v132;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4115_recIdents;
            RAST._IExpr _out1445;
            DCOMP._IOwnership _out1446;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1447;
            (this).GenExpr(_4112_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1445, out _out1446, out _out1447);
            _4113_recursiveGen = _out1445;
            _4114___v132 = _out1446;
            _4115_recIdents = _out1447;
            r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _4113_recursiveGen, _4111_format);
            RAST._IExpr _out1448;
            DCOMP._IOwnership _out1449;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1448, out _out1449);
            r = _out1448;
            resultingOwnership = _out1449;
            readIdents = _4115_recIdents;
            return ;
          }
        } else if (_source176.is_BitwiseNot) {
          DAST.Format._IUnaryOpFormat _4116_format = _4110___mcc_h39;
          DAST._IExpression _4117_e = _4109___mcc_h38;
          {
            RAST._IExpr _4118_recursiveGen;
            DCOMP._IOwnership _4119___v133;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4120_recIdents;
            RAST._IExpr _out1450;
            DCOMP._IOwnership _out1451;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1452;
            (this).GenExpr(_4117_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1450, out _out1451, out _out1452);
            _4118_recursiveGen = _out1450;
            _4119___v133 = _out1451;
            _4120_recIdents = _out1452;
            r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _4118_recursiveGen, _4116_format);
            RAST._IExpr _out1453;
            DCOMP._IOwnership _out1454;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1453, out _out1454);
            r = _out1453;
            resultingOwnership = _out1454;
            readIdents = _4120_recIdents;
            return ;
          }
        } else {
          DAST.Format._IUnaryOpFormat _4121_format = _4110___mcc_h39;
          DAST._IExpression _4122_e = _4109___mcc_h38;
          {
            RAST._IExpr _4123_recursiveGen;
            DCOMP._IOwnership _4124_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4125_recIdents;
            RAST._IExpr _out1455;
            DCOMP._IOwnership _out1456;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1457;
            (this).GenExpr(_4122_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1455, out _out1456, out _out1457);
            _4123_recursiveGen = _out1455;
            _4124_recOwned = _out1456;
            _4125_recIdents = _out1457;
            r = ((_4123_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out1458;
            DCOMP._IOwnership _out1459;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1458, out _out1459);
            r = _out1458;
            resultingOwnership = _out1459;
            readIdents = _4125_recIdents;
            return ;
          }
        }
      } else if (_source174.is_BinOp) {
        DAST._IBinOp _4126___mcc_h40 = _source174.dtor_op;
        DAST._IExpression _4127___mcc_h41 = _source174.dtor_left;
        DAST._IExpression _4128___mcc_h42 = _source174.dtor_right;
        DAST.Format._IBinaryOpFormat _4129___mcc_h43 = _source174.dtor_format2;
        RAST._IExpr _out1460;
        DCOMP._IOwnership _out1461;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1462;
        (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out1460, out _out1461, out _out1462);
        r = _out1460;
        resultingOwnership = _out1461;
        readIdents = _out1462;
      } else if (_source174.is_ArrayLen) {
        DAST._IExpression _4130___mcc_h44 = _source174.dtor_expr;
        BigInteger _4131___mcc_h45 = _source174.dtor_dim;
        BigInteger _4132_dim = _4131___mcc_h45;
        DAST._IExpression _4133_expr = _4130___mcc_h44;
        {
          RAST._IExpr _4134_recursiveGen;
          DCOMP._IOwnership _4135___v138;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4136_recIdents;
          RAST._IExpr _out1463;
          DCOMP._IOwnership _out1464;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1465;
          (this).GenExpr(_4133_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1463, out _out1464, out _out1465);
          _4134_recursiveGen = _out1463;
          _4135___v138 = _out1464;
          _4136_recIdents = _out1465;
          if ((_4132_dim).Sign == 0) {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), (_4134_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())")));
          } else {
            Dafny.ISequence<Dafny.Rune> _4137_s;
            _4137_s = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(m.borrow().len())")))._ToString(DCOMP.__default.IND);
            BigInteger _4138_i;
            _4138_i = BigInteger.One;
            while ((_4138_i) < (_4132_dim)) {
              _4137_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("m.borrow().get(0).map(|m| "), _4137_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"));
              _4138_i = (_4138_i) + (BigInteger.One);
            }
            r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_4134_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow().get(0).map(|m| ")), _4137_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"))));
          }
          RAST._IExpr _out1466;
          DCOMP._IOwnership _out1467;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1466, out _out1467);
          r = _out1466;
          resultingOwnership = _out1467;
          readIdents = _4136_recIdents;
          return ;
        }
      } else if (_source174.is_MapKeys) {
        DAST._IExpression _4139___mcc_h46 = _source174.dtor_expr;
        DAST._IExpression _4140_expr = _4139___mcc_h46;
        {
          RAST._IExpr _4141_recursiveGen;
          DCOMP._IOwnership _4142___v139;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4143_recIdents;
          RAST._IExpr _out1468;
          DCOMP._IOwnership _out1469;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1470;
          (this).GenExpr(_4140_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1468, out _out1469, out _out1470);
          _4141_recursiveGen = _out1468;
          _4142___v139 = _out1469;
          _4143_recIdents = _out1470;
          readIdents = _4143_recIdents;
          r = ((_4141_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1471;
          DCOMP._IOwnership _out1472;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1471, out _out1472);
          r = _out1471;
          resultingOwnership = _out1472;
          return ;
        }
      } else if (_source174.is_MapValues) {
        DAST._IExpression _4144___mcc_h47 = _source174.dtor_expr;
        DAST._IExpression _4145_expr = _4144___mcc_h47;
        {
          RAST._IExpr _4146_recursiveGen;
          DCOMP._IOwnership _4147___v140;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4148_recIdents;
          RAST._IExpr _out1473;
          DCOMP._IOwnership _out1474;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1475;
          (this).GenExpr(_4145_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1473, out _out1474, out _out1475);
          _4146_recursiveGen = _out1473;
          _4147___v140 = _out1474;
          _4148_recIdents = _out1475;
          readIdents = _4148_recIdents;
          r = ((_4146_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1476;
          DCOMP._IOwnership _out1477;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1476, out _out1477);
          r = _out1476;
          resultingOwnership = _out1477;
          return ;
        }
      } else if (_source174.is_Select) {
        DAST._IExpression _4149___mcc_h48 = _source174.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _4150___mcc_h49 = _source174.dtor_field;
        bool _4151___mcc_h50 = _source174.dtor_isConstant;
        bool _4152___mcc_h51 = _source174.dtor_onDatatype;
        DAST._IType _4153___mcc_h52 = _source174.dtor_fieldType;
        DAST._IExpression _source177 = _4149___mcc_h48;
        if (_source177.is_Literal) {
          DAST._ILiteral _4154___mcc_h53 = _source177.dtor_Literal_i_a0;
          DAST._IType _4155_fieldType = _4153___mcc_h52;
          bool _4156_isDatatype = _4152___mcc_h51;
          bool _4157_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4158_field = _4150___mcc_h49;
          DAST._IExpression _4159_on = _4149___mcc_h48;
          {
            if (_4156_isDatatype) {
              RAST._IExpr _4160_onExpr;
              DCOMP._IOwnership _4161_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4162_recIdents;
              RAST._IExpr _out1478;
              DCOMP._IOwnership _out1479;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1480;
              (this).GenExpr(_4159_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1478, out _out1479, out _out1480);
              _4160_onExpr = _out1478;
              _4161_onOwned = _out1479;
              _4162_recIdents = _out1480;
              r = ((_4160_onExpr).Sel(DCOMP.__default.escapeName(_4158_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4163_typ;
              RAST._IType _out1481;
              _out1481 = (this).GenType(_4155_fieldType, false, false);
              _4163_typ = _out1481;
              if (((_4163_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1482;
                DCOMP._IOwnership _out1483;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1482, out _out1483);
                r = _out1482;
                resultingOwnership = _out1483;
              }
              readIdents = _4162_recIdents;
            } else {
              RAST._IExpr _4164_onExpr;
              DCOMP._IOwnership _4165_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4166_recIdents;
              RAST._IExpr _out1484;
              DCOMP._IOwnership _out1485;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1486;
              (this).GenExpr(_4159_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1484, out _out1485, out _out1486);
              _4164_onExpr = _out1484;
              _4165_onOwned = _out1485;
              _4166_recIdents = _out1486;
              r = _4164_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4158_field));
              if (_4157_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4167_s;
                _4167_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4164_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4158_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4167_s);
              }
              DCOMP._IOwnership _4168_fromOwnership;
              _4168_fromOwnership = ((_4157_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1487;
              DCOMP._IOwnership _out1488;
              DCOMP.COMP.FromOwnership(r, _4168_fromOwnership, expectedOwnership, out _out1487, out _out1488);
              r = _out1487;
              resultingOwnership = _out1488;
              readIdents = _4166_recIdents;
            }
            return ;
          }
        } else if (_source177.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _4169___mcc_h55 = _source177.dtor_Ident_i_a0;
          DAST._IType _4170_fieldType = _4153___mcc_h52;
          bool _4171_isDatatype = _4152___mcc_h51;
          bool _4172_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4173_field = _4150___mcc_h49;
          DAST._IExpression _4174_on = _4149___mcc_h48;
          {
            if (_4171_isDatatype) {
              RAST._IExpr _4175_onExpr;
              DCOMP._IOwnership _4176_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4177_recIdents;
              RAST._IExpr _out1489;
              DCOMP._IOwnership _out1490;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1491;
              (this).GenExpr(_4174_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1489, out _out1490, out _out1491);
              _4175_onExpr = _out1489;
              _4176_onOwned = _out1490;
              _4177_recIdents = _out1491;
              r = ((_4175_onExpr).Sel(DCOMP.__default.escapeName(_4173_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4178_typ;
              RAST._IType _out1492;
              _out1492 = (this).GenType(_4170_fieldType, false, false);
              _4178_typ = _out1492;
              if (((_4178_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1493;
                DCOMP._IOwnership _out1494;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1493, out _out1494);
                r = _out1493;
                resultingOwnership = _out1494;
              }
              readIdents = _4177_recIdents;
            } else {
              RAST._IExpr _4179_onExpr;
              DCOMP._IOwnership _4180_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4181_recIdents;
              RAST._IExpr _out1495;
              DCOMP._IOwnership _out1496;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1497;
              (this).GenExpr(_4174_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1495, out _out1496, out _out1497);
              _4179_onExpr = _out1495;
              _4180_onOwned = _out1496;
              _4181_recIdents = _out1497;
              r = _4179_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4173_field));
              if (_4172_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4182_s;
                _4182_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4179_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4173_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4182_s);
              }
              DCOMP._IOwnership _4183_fromOwnership;
              _4183_fromOwnership = ((_4172_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1498;
              DCOMP._IOwnership _out1499;
              DCOMP.COMP.FromOwnership(r, _4183_fromOwnership, expectedOwnership, out _out1498, out _out1499);
              r = _out1498;
              resultingOwnership = _out1499;
              readIdents = _4181_recIdents;
            }
            return ;
          }
        } else if (_source177.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4184___mcc_h57 = _source177.dtor_Companion_i_a0;
          DAST._IType _4185_fieldType = _4153___mcc_h52;
          bool _4186_isDatatype = _4152___mcc_h51;
          bool _4187_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4188_field = _4150___mcc_h49;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4189_c = _4184___mcc_h57;
          {
            RAST._IExpr _4190_onExpr;
            DCOMP._IOwnership _4191_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4192_recIdents;
            RAST._IExpr _out1500;
            DCOMP._IOwnership _out1501;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1502;
            (this).GenExpr(DAST.Expression.create_Companion(_4189_c), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1500, out _out1501, out _out1502);
            _4190_onExpr = _out1500;
            _4191_onOwned = _out1501;
            _4192_recIdents = _out1502;
            r = ((_4190_onExpr).MSel(DCOMP.__default.escapeName(_4188_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out1503;
            DCOMP._IOwnership _out1504;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1503, out _out1504);
            r = _out1503;
            resultingOwnership = _out1504;
            readIdents = _4192_recIdents;
            return ;
          }
        } else if (_source177.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _4193___mcc_h59 = _source177.dtor_Tuple_i_a0;
          DAST._IType _4194_fieldType = _4153___mcc_h52;
          bool _4195_isDatatype = _4152___mcc_h51;
          bool _4196_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4197_field = _4150___mcc_h49;
          DAST._IExpression _4198_on = _4149___mcc_h48;
          {
            if (_4195_isDatatype) {
              RAST._IExpr _4199_onExpr;
              DCOMP._IOwnership _4200_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4201_recIdents;
              RAST._IExpr _out1505;
              DCOMP._IOwnership _out1506;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1507;
              (this).GenExpr(_4198_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1505, out _out1506, out _out1507);
              _4199_onExpr = _out1505;
              _4200_onOwned = _out1506;
              _4201_recIdents = _out1507;
              r = ((_4199_onExpr).Sel(DCOMP.__default.escapeName(_4197_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4202_typ;
              RAST._IType _out1508;
              _out1508 = (this).GenType(_4194_fieldType, false, false);
              _4202_typ = _out1508;
              if (((_4202_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1509;
                DCOMP._IOwnership _out1510;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1509, out _out1510);
                r = _out1509;
                resultingOwnership = _out1510;
              }
              readIdents = _4201_recIdents;
            } else {
              RAST._IExpr _4203_onExpr;
              DCOMP._IOwnership _4204_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4205_recIdents;
              RAST._IExpr _out1511;
              DCOMP._IOwnership _out1512;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1513;
              (this).GenExpr(_4198_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1511, out _out1512, out _out1513);
              _4203_onExpr = _out1511;
              _4204_onOwned = _out1512;
              _4205_recIdents = _out1513;
              r = _4203_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4197_field));
              if (_4196_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4206_s;
                _4206_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4203_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4197_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4206_s);
              }
              DCOMP._IOwnership _4207_fromOwnership;
              _4207_fromOwnership = ((_4196_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1514;
              DCOMP._IOwnership _out1515;
              DCOMP.COMP.FromOwnership(r, _4207_fromOwnership, expectedOwnership, out _out1514, out _out1515);
              r = _out1514;
              resultingOwnership = _out1515;
              readIdents = _4205_recIdents;
            }
            return ;
          }
        } else if (_source177.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4208___mcc_h61 = _source177.dtor_path;
          Dafny.ISequence<DAST._IType> _4209___mcc_h62 = _source177.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _4210___mcc_h63 = _source177.dtor_args;
          DAST._IType _4211_fieldType = _4153___mcc_h52;
          bool _4212_isDatatype = _4152___mcc_h51;
          bool _4213_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4214_field = _4150___mcc_h49;
          DAST._IExpression _4215_on = _4149___mcc_h48;
          {
            if (_4212_isDatatype) {
              RAST._IExpr _4216_onExpr;
              DCOMP._IOwnership _4217_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4218_recIdents;
              RAST._IExpr _out1516;
              DCOMP._IOwnership _out1517;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1518;
              (this).GenExpr(_4215_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1516, out _out1517, out _out1518);
              _4216_onExpr = _out1516;
              _4217_onOwned = _out1517;
              _4218_recIdents = _out1518;
              r = ((_4216_onExpr).Sel(DCOMP.__default.escapeName(_4214_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4219_typ;
              RAST._IType _out1519;
              _out1519 = (this).GenType(_4211_fieldType, false, false);
              _4219_typ = _out1519;
              if (((_4219_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1520;
                DCOMP._IOwnership _out1521;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1520, out _out1521);
                r = _out1520;
                resultingOwnership = _out1521;
              }
              readIdents = _4218_recIdents;
            } else {
              RAST._IExpr _4220_onExpr;
              DCOMP._IOwnership _4221_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4222_recIdents;
              RAST._IExpr _out1522;
              DCOMP._IOwnership _out1523;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1524;
              (this).GenExpr(_4215_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1522, out _out1523, out _out1524);
              _4220_onExpr = _out1522;
              _4221_onOwned = _out1523;
              _4222_recIdents = _out1524;
              r = _4220_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4214_field));
              if (_4213_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4223_s;
                _4223_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4220_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4214_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4223_s);
              }
              DCOMP._IOwnership _4224_fromOwnership;
              _4224_fromOwnership = ((_4213_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1525;
              DCOMP._IOwnership _out1526;
              DCOMP.COMP.FromOwnership(r, _4224_fromOwnership, expectedOwnership, out _out1525, out _out1526);
              r = _out1525;
              resultingOwnership = _out1526;
              readIdents = _4222_recIdents;
            }
            return ;
          }
        } else if (_source177.is_NewArray) {
          Dafny.ISequence<DAST._IExpression> _4225___mcc_h67 = _source177.dtor_dims;
          DAST._IType _4226___mcc_h68 = _source177.dtor_typ;
          DAST._IType _4227_fieldType = _4153___mcc_h52;
          bool _4228_isDatatype = _4152___mcc_h51;
          bool _4229_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4230_field = _4150___mcc_h49;
          DAST._IExpression _4231_on = _4149___mcc_h48;
          {
            if (_4228_isDatatype) {
              RAST._IExpr _4232_onExpr;
              DCOMP._IOwnership _4233_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4234_recIdents;
              RAST._IExpr _out1527;
              DCOMP._IOwnership _out1528;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1529;
              (this).GenExpr(_4231_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1527, out _out1528, out _out1529);
              _4232_onExpr = _out1527;
              _4233_onOwned = _out1528;
              _4234_recIdents = _out1529;
              r = ((_4232_onExpr).Sel(DCOMP.__default.escapeName(_4230_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4235_typ;
              RAST._IType _out1530;
              _out1530 = (this).GenType(_4227_fieldType, false, false);
              _4235_typ = _out1530;
              if (((_4235_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1531;
                DCOMP._IOwnership _out1532;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1531, out _out1532);
                r = _out1531;
                resultingOwnership = _out1532;
              }
              readIdents = _4234_recIdents;
            } else {
              RAST._IExpr _4236_onExpr;
              DCOMP._IOwnership _4237_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4238_recIdents;
              RAST._IExpr _out1533;
              DCOMP._IOwnership _out1534;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1535;
              (this).GenExpr(_4231_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1533, out _out1534, out _out1535);
              _4236_onExpr = _out1533;
              _4237_onOwned = _out1534;
              _4238_recIdents = _out1535;
              r = _4236_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4230_field));
              if (_4229_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4239_s;
                _4239_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4236_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4230_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4239_s);
              }
              DCOMP._IOwnership _4240_fromOwnership;
              _4240_fromOwnership = ((_4229_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1536;
              DCOMP._IOwnership _out1537;
              DCOMP.COMP.FromOwnership(r, _4240_fromOwnership, expectedOwnership, out _out1536, out _out1537);
              r = _out1536;
              resultingOwnership = _out1537;
              readIdents = _4238_recIdents;
            }
            return ;
          }
        } else if (_source177.is_DatatypeValue) {
          DAST._IDatatypeType _4241___mcc_h71 = _source177.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _4242___mcc_h72 = _source177.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _4243___mcc_h73 = _source177.dtor_variant;
          bool _4244___mcc_h74 = _source177.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _4245___mcc_h75 = _source177.dtor_contents;
          DAST._IType _4246_fieldType = _4153___mcc_h52;
          bool _4247_isDatatype = _4152___mcc_h51;
          bool _4248_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4249_field = _4150___mcc_h49;
          DAST._IExpression _4250_on = _4149___mcc_h48;
          {
            if (_4247_isDatatype) {
              RAST._IExpr _4251_onExpr;
              DCOMP._IOwnership _4252_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4253_recIdents;
              RAST._IExpr _out1538;
              DCOMP._IOwnership _out1539;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1540;
              (this).GenExpr(_4250_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1538, out _out1539, out _out1540);
              _4251_onExpr = _out1538;
              _4252_onOwned = _out1539;
              _4253_recIdents = _out1540;
              r = ((_4251_onExpr).Sel(DCOMP.__default.escapeName(_4249_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4254_typ;
              RAST._IType _out1541;
              _out1541 = (this).GenType(_4246_fieldType, false, false);
              _4254_typ = _out1541;
              if (((_4254_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1542;
                DCOMP._IOwnership _out1543;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1542, out _out1543);
                r = _out1542;
                resultingOwnership = _out1543;
              }
              readIdents = _4253_recIdents;
            } else {
              RAST._IExpr _4255_onExpr;
              DCOMP._IOwnership _4256_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4257_recIdents;
              RAST._IExpr _out1544;
              DCOMP._IOwnership _out1545;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1546;
              (this).GenExpr(_4250_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1544, out _out1545, out _out1546);
              _4255_onExpr = _out1544;
              _4256_onOwned = _out1545;
              _4257_recIdents = _out1546;
              r = _4255_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4249_field));
              if (_4248_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4258_s;
                _4258_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4255_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4249_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4258_s);
              }
              DCOMP._IOwnership _4259_fromOwnership;
              _4259_fromOwnership = ((_4248_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1547;
              DCOMP._IOwnership _out1548;
              DCOMP.COMP.FromOwnership(r, _4259_fromOwnership, expectedOwnership, out _out1547, out _out1548);
              r = _out1547;
              resultingOwnership = _out1548;
              readIdents = _4257_recIdents;
            }
            return ;
          }
        } else if (_source177.is_Convert) {
          DAST._IExpression _4260___mcc_h81 = _source177.dtor_value;
          DAST._IType _4261___mcc_h82 = _source177.dtor_from;
          DAST._IType _4262___mcc_h83 = _source177.dtor_typ;
          DAST._IType _4263_fieldType = _4153___mcc_h52;
          bool _4264_isDatatype = _4152___mcc_h51;
          bool _4265_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4266_field = _4150___mcc_h49;
          DAST._IExpression _4267_on = _4149___mcc_h48;
          {
            if (_4264_isDatatype) {
              RAST._IExpr _4268_onExpr;
              DCOMP._IOwnership _4269_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4270_recIdents;
              RAST._IExpr _out1549;
              DCOMP._IOwnership _out1550;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1551;
              (this).GenExpr(_4267_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1549, out _out1550, out _out1551);
              _4268_onExpr = _out1549;
              _4269_onOwned = _out1550;
              _4270_recIdents = _out1551;
              r = ((_4268_onExpr).Sel(DCOMP.__default.escapeName(_4266_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4271_typ;
              RAST._IType _out1552;
              _out1552 = (this).GenType(_4263_fieldType, false, false);
              _4271_typ = _out1552;
              if (((_4271_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1553;
                DCOMP._IOwnership _out1554;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1553, out _out1554);
                r = _out1553;
                resultingOwnership = _out1554;
              }
              readIdents = _4270_recIdents;
            } else {
              RAST._IExpr _4272_onExpr;
              DCOMP._IOwnership _4273_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4274_recIdents;
              RAST._IExpr _out1555;
              DCOMP._IOwnership _out1556;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1557;
              (this).GenExpr(_4267_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1555, out _out1556, out _out1557);
              _4272_onExpr = _out1555;
              _4273_onOwned = _out1556;
              _4274_recIdents = _out1557;
              r = _4272_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4266_field));
              if (_4265_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4275_s;
                _4275_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4272_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4266_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4275_s);
              }
              DCOMP._IOwnership _4276_fromOwnership;
              _4276_fromOwnership = ((_4265_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1558;
              DCOMP._IOwnership _out1559;
              DCOMP.COMP.FromOwnership(r, _4276_fromOwnership, expectedOwnership, out _out1558, out _out1559);
              r = _out1558;
              resultingOwnership = _out1559;
              readIdents = _4274_recIdents;
            }
            return ;
          }
        } else if (_source177.is_SeqConstruct) {
          DAST._IExpression _4277___mcc_h87 = _source177.dtor_length;
          DAST._IExpression _4278___mcc_h88 = _source177.dtor_elem;
          DAST._IType _4279_fieldType = _4153___mcc_h52;
          bool _4280_isDatatype = _4152___mcc_h51;
          bool _4281_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4282_field = _4150___mcc_h49;
          DAST._IExpression _4283_on = _4149___mcc_h48;
          {
            if (_4280_isDatatype) {
              RAST._IExpr _4284_onExpr;
              DCOMP._IOwnership _4285_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4286_recIdents;
              RAST._IExpr _out1560;
              DCOMP._IOwnership _out1561;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1562;
              (this).GenExpr(_4283_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1560, out _out1561, out _out1562);
              _4284_onExpr = _out1560;
              _4285_onOwned = _out1561;
              _4286_recIdents = _out1562;
              r = ((_4284_onExpr).Sel(DCOMP.__default.escapeName(_4282_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4287_typ;
              RAST._IType _out1563;
              _out1563 = (this).GenType(_4279_fieldType, false, false);
              _4287_typ = _out1563;
              if (((_4287_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1564;
                DCOMP._IOwnership _out1565;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1564, out _out1565);
                r = _out1564;
                resultingOwnership = _out1565;
              }
              readIdents = _4286_recIdents;
            } else {
              RAST._IExpr _4288_onExpr;
              DCOMP._IOwnership _4289_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4290_recIdents;
              RAST._IExpr _out1566;
              DCOMP._IOwnership _out1567;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1568;
              (this).GenExpr(_4283_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1566, out _out1567, out _out1568);
              _4288_onExpr = _out1566;
              _4289_onOwned = _out1567;
              _4290_recIdents = _out1568;
              r = _4288_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4282_field));
              if (_4281_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4291_s;
                _4291_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4288_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4282_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4291_s);
              }
              DCOMP._IOwnership _4292_fromOwnership;
              _4292_fromOwnership = ((_4281_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1569;
              DCOMP._IOwnership _out1570;
              DCOMP.COMP.FromOwnership(r, _4292_fromOwnership, expectedOwnership, out _out1569, out _out1570);
              r = _out1569;
              resultingOwnership = _out1570;
              readIdents = _4290_recIdents;
            }
            return ;
          }
        } else if (_source177.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _4293___mcc_h91 = _source177.dtor_elements;
          DAST._IType _4294___mcc_h92 = _source177.dtor_typ;
          DAST._IType _4295_fieldType = _4153___mcc_h52;
          bool _4296_isDatatype = _4152___mcc_h51;
          bool _4297_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4298_field = _4150___mcc_h49;
          DAST._IExpression _4299_on = _4149___mcc_h48;
          {
            if (_4296_isDatatype) {
              RAST._IExpr _4300_onExpr;
              DCOMP._IOwnership _4301_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4302_recIdents;
              RAST._IExpr _out1571;
              DCOMP._IOwnership _out1572;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1573;
              (this).GenExpr(_4299_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1571, out _out1572, out _out1573);
              _4300_onExpr = _out1571;
              _4301_onOwned = _out1572;
              _4302_recIdents = _out1573;
              r = ((_4300_onExpr).Sel(DCOMP.__default.escapeName(_4298_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4303_typ;
              RAST._IType _out1574;
              _out1574 = (this).GenType(_4295_fieldType, false, false);
              _4303_typ = _out1574;
              if (((_4303_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1575;
                DCOMP._IOwnership _out1576;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1575, out _out1576);
                r = _out1575;
                resultingOwnership = _out1576;
              }
              readIdents = _4302_recIdents;
            } else {
              RAST._IExpr _4304_onExpr;
              DCOMP._IOwnership _4305_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4306_recIdents;
              RAST._IExpr _out1577;
              DCOMP._IOwnership _out1578;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1579;
              (this).GenExpr(_4299_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1577, out _out1578, out _out1579);
              _4304_onExpr = _out1577;
              _4305_onOwned = _out1578;
              _4306_recIdents = _out1579;
              r = _4304_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4298_field));
              if (_4297_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4307_s;
                _4307_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4304_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4298_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4307_s);
              }
              DCOMP._IOwnership _4308_fromOwnership;
              _4308_fromOwnership = ((_4297_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1580;
              DCOMP._IOwnership _out1581;
              DCOMP.COMP.FromOwnership(r, _4308_fromOwnership, expectedOwnership, out _out1580, out _out1581);
              r = _out1580;
              resultingOwnership = _out1581;
              readIdents = _4306_recIdents;
            }
            return ;
          }
        } else if (_source177.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _4309___mcc_h95 = _source177.dtor_elements;
          DAST._IType _4310_fieldType = _4153___mcc_h52;
          bool _4311_isDatatype = _4152___mcc_h51;
          bool _4312_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4313_field = _4150___mcc_h49;
          DAST._IExpression _4314_on = _4149___mcc_h48;
          {
            if (_4311_isDatatype) {
              RAST._IExpr _4315_onExpr;
              DCOMP._IOwnership _4316_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4317_recIdents;
              RAST._IExpr _out1582;
              DCOMP._IOwnership _out1583;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1584;
              (this).GenExpr(_4314_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1582, out _out1583, out _out1584);
              _4315_onExpr = _out1582;
              _4316_onOwned = _out1583;
              _4317_recIdents = _out1584;
              r = ((_4315_onExpr).Sel(DCOMP.__default.escapeName(_4313_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4318_typ;
              RAST._IType _out1585;
              _out1585 = (this).GenType(_4310_fieldType, false, false);
              _4318_typ = _out1585;
              if (((_4318_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1586;
                DCOMP._IOwnership _out1587;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1586, out _out1587);
                r = _out1586;
                resultingOwnership = _out1587;
              }
              readIdents = _4317_recIdents;
            } else {
              RAST._IExpr _4319_onExpr;
              DCOMP._IOwnership _4320_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4321_recIdents;
              RAST._IExpr _out1588;
              DCOMP._IOwnership _out1589;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1590;
              (this).GenExpr(_4314_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1588, out _out1589, out _out1590);
              _4319_onExpr = _out1588;
              _4320_onOwned = _out1589;
              _4321_recIdents = _out1590;
              r = _4319_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4313_field));
              if (_4312_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4322_s;
                _4322_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4319_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4313_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4322_s);
              }
              DCOMP._IOwnership _4323_fromOwnership;
              _4323_fromOwnership = ((_4312_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1591;
              DCOMP._IOwnership _out1592;
              DCOMP.COMP.FromOwnership(r, _4323_fromOwnership, expectedOwnership, out _out1591, out _out1592);
              r = _out1591;
              resultingOwnership = _out1592;
              readIdents = _4321_recIdents;
            }
            return ;
          }
        } else if (_source177.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _4324___mcc_h97 = _source177.dtor_elements;
          DAST._IType _4325_fieldType = _4153___mcc_h52;
          bool _4326_isDatatype = _4152___mcc_h51;
          bool _4327_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4328_field = _4150___mcc_h49;
          DAST._IExpression _4329_on = _4149___mcc_h48;
          {
            if (_4326_isDatatype) {
              RAST._IExpr _4330_onExpr;
              DCOMP._IOwnership _4331_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4332_recIdents;
              RAST._IExpr _out1593;
              DCOMP._IOwnership _out1594;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1595;
              (this).GenExpr(_4329_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1593, out _out1594, out _out1595);
              _4330_onExpr = _out1593;
              _4331_onOwned = _out1594;
              _4332_recIdents = _out1595;
              r = ((_4330_onExpr).Sel(DCOMP.__default.escapeName(_4328_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4333_typ;
              RAST._IType _out1596;
              _out1596 = (this).GenType(_4325_fieldType, false, false);
              _4333_typ = _out1596;
              if (((_4333_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1597;
                DCOMP._IOwnership _out1598;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1597, out _out1598);
                r = _out1597;
                resultingOwnership = _out1598;
              }
              readIdents = _4332_recIdents;
            } else {
              RAST._IExpr _4334_onExpr;
              DCOMP._IOwnership _4335_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4336_recIdents;
              RAST._IExpr _out1599;
              DCOMP._IOwnership _out1600;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1601;
              (this).GenExpr(_4329_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1599, out _out1600, out _out1601);
              _4334_onExpr = _out1599;
              _4335_onOwned = _out1600;
              _4336_recIdents = _out1601;
              r = _4334_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4328_field));
              if (_4327_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4337_s;
                _4337_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4334_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4328_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4337_s);
              }
              DCOMP._IOwnership _4338_fromOwnership;
              _4338_fromOwnership = ((_4327_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1602;
              DCOMP._IOwnership _out1603;
              DCOMP.COMP.FromOwnership(r, _4338_fromOwnership, expectedOwnership, out _out1602, out _out1603);
              r = _out1602;
              resultingOwnership = _out1603;
              readIdents = _4336_recIdents;
            }
            return ;
          }
        } else if (_source177.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _4339___mcc_h99 = _source177.dtor_mapElems;
          DAST._IType _4340_fieldType = _4153___mcc_h52;
          bool _4341_isDatatype = _4152___mcc_h51;
          bool _4342_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4343_field = _4150___mcc_h49;
          DAST._IExpression _4344_on = _4149___mcc_h48;
          {
            if (_4341_isDatatype) {
              RAST._IExpr _4345_onExpr;
              DCOMP._IOwnership _4346_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4347_recIdents;
              RAST._IExpr _out1604;
              DCOMP._IOwnership _out1605;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1606;
              (this).GenExpr(_4344_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1604, out _out1605, out _out1606);
              _4345_onExpr = _out1604;
              _4346_onOwned = _out1605;
              _4347_recIdents = _out1606;
              r = ((_4345_onExpr).Sel(DCOMP.__default.escapeName(_4343_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4348_typ;
              RAST._IType _out1607;
              _out1607 = (this).GenType(_4340_fieldType, false, false);
              _4348_typ = _out1607;
              if (((_4348_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1608;
                DCOMP._IOwnership _out1609;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1608, out _out1609);
                r = _out1608;
                resultingOwnership = _out1609;
              }
              readIdents = _4347_recIdents;
            } else {
              RAST._IExpr _4349_onExpr;
              DCOMP._IOwnership _4350_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4351_recIdents;
              RAST._IExpr _out1610;
              DCOMP._IOwnership _out1611;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1612;
              (this).GenExpr(_4344_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1610, out _out1611, out _out1612);
              _4349_onExpr = _out1610;
              _4350_onOwned = _out1611;
              _4351_recIdents = _out1612;
              r = _4349_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4343_field));
              if (_4342_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4352_s;
                _4352_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4349_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4343_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4352_s);
              }
              DCOMP._IOwnership _4353_fromOwnership;
              _4353_fromOwnership = ((_4342_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1613;
              DCOMP._IOwnership _out1614;
              DCOMP.COMP.FromOwnership(r, _4353_fromOwnership, expectedOwnership, out _out1613, out _out1614);
              r = _out1613;
              resultingOwnership = _out1614;
              readIdents = _4351_recIdents;
            }
            return ;
          }
        } else if (_source177.is_MapBuilder) {
          DAST._IType _4354___mcc_h101 = _source177.dtor_keyType;
          DAST._IType _4355___mcc_h102 = _source177.dtor_valueType;
          DAST._IType _4356_fieldType = _4153___mcc_h52;
          bool _4357_isDatatype = _4152___mcc_h51;
          bool _4358_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4359_field = _4150___mcc_h49;
          DAST._IExpression _4360_on = _4149___mcc_h48;
          {
            if (_4357_isDatatype) {
              RAST._IExpr _4361_onExpr;
              DCOMP._IOwnership _4362_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4363_recIdents;
              RAST._IExpr _out1615;
              DCOMP._IOwnership _out1616;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1617;
              (this).GenExpr(_4360_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1615, out _out1616, out _out1617);
              _4361_onExpr = _out1615;
              _4362_onOwned = _out1616;
              _4363_recIdents = _out1617;
              r = ((_4361_onExpr).Sel(DCOMP.__default.escapeName(_4359_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4364_typ;
              RAST._IType _out1618;
              _out1618 = (this).GenType(_4356_fieldType, false, false);
              _4364_typ = _out1618;
              if (((_4364_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1619;
                DCOMP._IOwnership _out1620;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1619, out _out1620);
                r = _out1619;
                resultingOwnership = _out1620;
              }
              readIdents = _4363_recIdents;
            } else {
              RAST._IExpr _4365_onExpr;
              DCOMP._IOwnership _4366_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4367_recIdents;
              RAST._IExpr _out1621;
              DCOMP._IOwnership _out1622;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1623;
              (this).GenExpr(_4360_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1621, out _out1622, out _out1623);
              _4365_onExpr = _out1621;
              _4366_onOwned = _out1622;
              _4367_recIdents = _out1623;
              r = _4365_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4359_field));
              if (_4358_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4368_s;
                _4368_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4365_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4359_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4368_s);
              }
              DCOMP._IOwnership _4369_fromOwnership;
              _4369_fromOwnership = ((_4358_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1624;
              DCOMP._IOwnership _out1625;
              DCOMP.COMP.FromOwnership(r, _4369_fromOwnership, expectedOwnership, out _out1624, out _out1625);
              r = _out1624;
              resultingOwnership = _out1625;
              readIdents = _4367_recIdents;
            }
            return ;
          }
        } else if (_source177.is_SeqUpdate) {
          DAST._IExpression _4370___mcc_h105 = _source177.dtor_expr;
          DAST._IExpression _4371___mcc_h106 = _source177.dtor_indexExpr;
          DAST._IExpression _4372___mcc_h107 = _source177.dtor_value;
          DAST._IType _4373_fieldType = _4153___mcc_h52;
          bool _4374_isDatatype = _4152___mcc_h51;
          bool _4375_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4376_field = _4150___mcc_h49;
          DAST._IExpression _4377_on = _4149___mcc_h48;
          {
            if (_4374_isDatatype) {
              RAST._IExpr _4378_onExpr;
              DCOMP._IOwnership _4379_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4380_recIdents;
              RAST._IExpr _out1626;
              DCOMP._IOwnership _out1627;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1628;
              (this).GenExpr(_4377_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1626, out _out1627, out _out1628);
              _4378_onExpr = _out1626;
              _4379_onOwned = _out1627;
              _4380_recIdents = _out1628;
              r = ((_4378_onExpr).Sel(DCOMP.__default.escapeName(_4376_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4381_typ;
              RAST._IType _out1629;
              _out1629 = (this).GenType(_4373_fieldType, false, false);
              _4381_typ = _out1629;
              if (((_4381_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1630;
                DCOMP._IOwnership _out1631;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1630, out _out1631);
                r = _out1630;
                resultingOwnership = _out1631;
              }
              readIdents = _4380_recIdents;
            } else {
              RAST._IExpr _4382_onExpr;
              DCOMP._IOwnership _4383_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4384_recIdents;
              RAST._IExpr _out1632;
              DCOMP._IOwnership _out1633;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1634;
              (this).GenExpr(_4377_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1632, out _out1633, out _out1634);
              _4382_onExpr = _out1632;
              _4383_onOwned = _out1633;
              _4384_recIdents = _out1634;
              r = _4382_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4376_field));
              if (_4375_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4385_s;
                _4385_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4382_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4376_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4385_s);
              }
              DCOMP._IOwnership _4386_fromOwnership;
              _4386_fromOwnership = ((_4375_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1635;
              DCOMP._IOwnership _out1636;
              DCOMP.COMP.FromOwnership(r, _4386_fromOwnership, expectedOwnership, out _out1635, out _out1636);
              r = _out1635;
              resultingOwnership = _out1636;
              readIdents = _4384_recIdents;
            }
            return ;
          }
        } else if (_source177.is_MapUpdate) {
          DAST._IExpression _4387___mcc_h111 = _source177.dtor_expr;
          DAST._IExpression _4388___mcc_h112 = _source177.dtor_indexExpr;
          DAST._IExpression _4389___mcc_h113 = _source177.dtor_value;
          DAST._IType _4390_fieldType = _4153___mcc_h52;
          bool _4391_isDatatype = _4152___mcc_h51;
          bool _4392_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4393_field = _4150___mcc_h49;
          DAST._IExpression _4394_on = _4149___mcc_h48;
          {
            if (_4391_isDatatype) {
              RAST._IExpr _4395_onExpr;
              DCOMP._IOwnership _4396_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4397_recIdents;
              RAST._IExpr _out1637;
              DCOMP._IOwnership _out1638;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1639;
              (this).GenExpr(_4394_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1637, out _out1638, out _out1639);
              _4395_onExpr = _out1637;
              _4396_onOwned = _out1638;
              _4397_recIdents = _out1639;
              r = ((_4395_onExpr).Sel(DCOMP.__default.escapeName(_4393_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4398_typ;
              RAST._IType _out1640;
              _out1640 = (this).GenType(_4390_fieldType, false, false);
              _4398_typ = _out1640;
              if (((_4398_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1641;
                DCOMP._IOwnership _out1642;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1641, out _out1642);
                r = _out1641;
                resultingOwnership = _out1642;
              }
              readIdents = _4397_recIdents;
            } else {
              RAST._IExpr _4399_onExpr;
              DCOMP._IOwnership _4400_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4401_recIdents;
              RAST._IExpr _out1643;
              DCOMP._IOwnership _out1644;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1645;
              (this).GenExpr(_4394_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1643, out _out1644, out _out1645);
              _4399_onExpr = _out1643;
              _4400_onOwned = _out1644;
              _4401_recIdents = _out1645;
              r = _4399_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4393_field));
              if (_4392_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4402_s;
                _4402_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4399_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4393_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4402_s);
              }
              DCOMP._IOwnership _4403_fromOwnership;
              _4403_fromOwnership = ((_4392_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1646;
              DCOMP._IOwnership _out1647;
              DCOMP.COMP.FromOwnership(r, _4403_fromOwnership, expectedOwnership, out _out1646, out _out1647);
              r = _out1646;
              resultingOwnership = _out1647;
              readIdents = _4401_recIdents;
            }
            return ;
          }
        } else if (_source177.is_SetBuilder) {
          DAST._IType _4404___mcc_h117 = _source177.dtor_elemType;
          DAST._IType _4405_fieldType = _4153___mcc_h52;
          bool _4406_isDatatype = _4152___mcc_h51;
          bool _4407_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4408_field = _4150___mcc_h49;
          DAST._IExpression _4409_on = _4149___mcc_h48;
          {
            if (_4406_isDatatype) {
              RAST._IExpr _4410_onExpr;
              DCOMP._IOwnership _4411_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4412_recIdents;
              RAST._IExpr _out1648;
              DCOMP._IOwnership _out1649;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1650;
              (this).GenExpr(_4409_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1648, out _out1649, out _out1650);
              _4410_onExpr = _out1648;
              _4411_onOwned = _out1649;
              _4412_recIdents = _out1650;
              r = ((_4410_onExpr).Sel(DCOMP.__default.escapeName(_4408_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4413_typ;
              RAST._IType _out1651;
              _out1651 = (this).GenType(_4405_fieldType, false, false);
              _4413_typ = _out1651;
              if (((_4413_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1652;
                DCOMP._IOwnership _out1653;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1652, out _out1653);
                r = _out1652;
                resultingOwnership = _out1653;
              }
              readIdents = _4412_recIdents;
            } else {
              RAST._IExpr _4414_onExpr;
              DCOMP._IOwnership _4415_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4416_recIdents;
              RAST._IExpr _out1654;
              DCOMP._IOwnership _out1655;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1656;
              (this).GenExpr(_4409_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1654, out _out1655, out _out1656);
              _4414_onExpr = _out1654;
              _4415_onOwned = _out1655;
              _4416_recIdents = _out1656;
              r = _4414_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4408_field));
              if (_4407_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4417_s;
                _4417_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4414_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4408_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4417_s);
              }
              DCOMP._IOwnership _4418_fromOwnership;
              _4418_fromOwnership = ((_4407_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1657;
              DCOMP._IOwnership _out1658;
              DCOMP.COMP.FromOwnership(r, _4418_fromOwnership, expectedOwnership, out _out1657, out _out1658);
              r = _out1657;
              resultingOwnership = _out1658;
              readIdents = _4416_recIdents;
            }
            return ;
          }
        } else if (_source177.is_ToMultiset) {
          DAST._IExpression _4419___mcc_h119 = _source177.dtor_ToMultiset_i_a0;
          DAST._IType _4420_fieldType = _4153___mcc_h52;
          bool _4421_isDatatype = _4152___mcc_h51;
          bool _4422_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4423_field = _4150___mcc_h49;
          DAST._IExpression _4424_on = _4149___mcc_h48;
          {
            if (_4421_isDatatype) {
              RAST._IExpr _4425_onExpr;
              DCOMP._IOwnership _4426_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4427_recIdents;
              RAST._IExpr _out1659;
              DCOMP._IOwnership _out1660;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1661;
              (this).GenExpr(_4424_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1659, out _out1660, out _out1661);
              _4425_onExpr = _out1659;
              _4426_onOwned = _out1660;
              _4427_recIdents = _out1661;
              r = ((_4425_onExpr).Sel(DCOMP.__default.escapeName(_4423_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4428_typ;
              RAST._IType _out1662;
              _out1662 = (this).GenType(_4420_fieldType, false, false);
              _4428_typ = _out1662;
              if (((_4428_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1663;
                DCOMP._IOwnership _out1664;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1663, out _out1664);
                r = _out1663;
                resultingOwnership = _out1664;
              }
              readIdents = _4427_recIdents;
            } else {
              RAST._IExpr _4429_onExpr;
              DCOMP._IOwnership _4430_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4431_recIdents;
              RAST._IExpr _out1665;
              DCOMP._IOwnership _out1666;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1667;
              (this).GenExpr(_4424_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1665, out _out1666, out _out1667);
              _4429_onExpr = _out1665;
              _4430_onOwned = _out1666;
              _4431_recIdents = _out1667;
              r = _4429_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4423_field));
              if (_4422_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4432_s;
                _4432_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4429_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4423_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4432_s);
              }
              DCOMP._IOwnership _4433_fromOwnership;
              _4433_fromOwnership = ((_4422_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1668;
              DCOMP._IOwnership _out1669;
              DCOMP.COMP.FromOwnership(r, _4433_fromOwnership, expectedOwnership, out _out1668, out _out1669);
              r = _out1668;
              resultingOwnership = _out1669;
              readIdents = _4431_recIdents;
            }
            return ;
          }
        } else if (_source177.is_This) {
          DAST._IType _4434_fieldType = _4153___mcc_h52;
          bool _4435_isDatatype = _4152___mcc_h51;
          bool _4436_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4437_field = _4150___mcc_h49;
          DAST._IExpression _4438_on = _4149___mcc_h48;
          {
            if (_4435_isDatatype) {
              RAST._IExpr _4439_onExpr;
              DCOMP._IOwnership _4440_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4441_recIdents;
              RAST._IExpr _out1670;
              DCOMP._IOwnership _out1671;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1672;
              (this).GenExpr(_4438_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1670, out _out1671, out _out1672);
              _4439_onExpr = _out1670;
              _4440_onOwned = _out1671;
              _4441_recIdents = _out1672;
              r = ((_4439_onExpr).Sel(DCOMP.__default.escapeName(_4437_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4442_typ;
              RAST._IType _out1673;
              _out1673 = (this).GenType(_4434_fieldType, false, false);
              _4442_typ = _out1673;
              if (((_4442_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1674;
                DCOMP._IOwnership _out1675;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1674, out _out1675);
                r = _out1674;
                resultingOwnership = _out1675;
              }
              readIdents = _4441_recIdents;
            } else {
              RAST._IExpr _4443_onExpr;
              DCOMP._IOwnership _4444_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4445_recIdents;
              RAST._IExpr _out1676;
              DCOMP._IOwnership _out1677;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1678;
              (this).GenExpr(_4438_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1676, out _out1677, out _out1678);
              _4443_onExpr = _out1676;
              _4444_onOwned = _out1677;
              _4445_recIdents = _out1678;
              r = _4443_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4437_field));
              if (_4436_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4446_s;
                _4446_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4443_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4437_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4446_s);
              }
              DCOMP._IOwnership _4447_fromOwnership;
              _4447_fromOwnership = ((_4436_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1679;
              DCOMP._IOwnership _out1680;
              DCOMP.COMP.FromOwnership(r, _4447_fromOwnership, expectedOwnership, out _out1679, out _out1680);
              r = _out1679;
              resultingOwnership = _out1680;
              readIdents = _4445_recIdents;
            }
            return ;
          }
        } else if (_source177.is_Ite) {
          DAST._IExpression _4448___mcc_h121 = _source177.dtor_cond;
          DAST._IExpression _4449___mcc_h122 = _source177.dtor_thn;
          DAST._IExpression _4450___mcc_h123 = _source177.dtor_els;
          DAST._IType _4451_fieldType = _4153___mcc_h52;
          bool _4452_isDatatype = _4152___mcc_h51;
          bool _4453_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4454_field = _4150___mcc_h49;
          DAST._IExpression _4455_on = _4149___mcc_h48;
          {
            if (_4452_isDatatype) {
              RAST._IExpr _4456_onExpr;
              DCOMP._IOwnership _4457_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4458_recIdents;
              RAST._IExpr _out1681;
              DCOMP._IOwnership _out1682;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1683;
              (this).GenExpr(_4455_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1681, out _out1682, out _out1683);
              _4456_onExpr = _out1681;
              _4457_onOwned = _out1682;
              _4458_recIdents = _out1683;
              r = ((_4456_onExpr).Sel(DCOMP.__default.escapeName(_4454_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4459_typ;
              RAST._IType _out1684;
              _out1684 = (this).GenType(_4451_fieldType, false, false);
              _4459_typ = _out1684;
              if (((_4459_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1685;
                DCOMP._IOwnership _out1686;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1685, out _out1686);
                r = _out1685;
                resultingOwnership = _out1686;
              }
              readIdents = _4458_recIdents;
            } else {
              RAST._IExpr _4460_onExpr;
              DCOMP._IOwnership _4461_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4462_recIdents;
              RAST._IExpr _out1687;
              DCOMP._IOwnership _out1688;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1689;
              (this).GenExpr(_4455_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1687, out _out1688, out _out1689);
              _4460_onExpr = _out1687;
              _4461_onOwned = _out1688;
              _4462_recIdents = _out1689;
              r = _4460_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4454_field));
              if (_4453_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4463_s;
                _4463_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4460_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4454_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4463_s);
              }
              DCOMP._IOwnership _4464_fromOwnership;
              _4464_fromOwnership = ((_4453_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1690;
              DCOMP._IOwnership _out1691;
              DCOMP.COMP.FromOwnership(r, _4464_fromOwnership, expectedOwnership, out _out1690, out _out1691);
              r = _out1690;
              resultingOwnership = _out1691;
              readIdents = _4462_recIdents;
            }
            return ;
          }
        } else if (_source177.is_UnOp) {
          DAST._IUnaryOp _4465___mcc_h127 = _source177.dtor_unOp;
          DAST._IExpression _4466___mcc_h128 = _source177.dtor_expr;
          DAST.Format._IUnaryOpFormat _4467___mcc_h129 = _source177.dtor_format1;
          DAST._IType _4468_fieldType = _4153___mcc_h52;
          bool _4469_isDatatype = _4152___mcc_h51;
          bool _4470_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4471_field = _4150___mcc_h49;
          DAST._IExpression _4472_on = _4149___mcc_h48;
          {
            if (_4469_isDatatype) {
              RAST._IExpr _4473_onExpr;
              DCOMP._IOwnership _4474_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4475_recIdents;
              RAST._IExpr _out1692;
              DCOMP._IOwnership _out1693;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1694;
              (this).GenExpr(_4472_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1692, out _out1693, out _out1694);
              _4473_onExpr = _out1692;
              _4474_onOwned = _out1693;
              _4475_recIdents = _out1694;
              r = ((_4473_onExpr).Sel(DCOMP.__default.escapeName(_4471_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4476_typ;
              RAST._IType _out1695;
              _out1695 = (this).GenType(_4468_fieldType, false, false);
              _4476_typ = _out1695;
              if (((_4476_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1696;
                DCOMP._IOwnership _out1697;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1696, out _out1697);
                r = _out1696;
                resultingOwnership = _out1697;
              }
              readIdents = _4475_recIdents;
            } else {
              RAST._IExpr _4477_onExpr;
              DCOMP._IOwnership _4478_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4479_recIdents;
              RAST._IExpr _out1698;
              DCOMP._IOwnership _out1699;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1700;
              (this).GenExpr(_4472_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1698, out _out1699, out _out1700);
              _4477_onExpr = _out1698;
              _4478_onOwned = _out1699;
              _4479_recIdents = _out1700;
              r = _4477_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4471_field));
              if (_4470_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4480_s;
                _4480_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4477_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4471_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4480_s);
              }
              DCOMP._IOwnership _4481_fromOwnership;
              _4481_fromOwnership = ((_4470_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1701;
              DCOMP._IOwnership _out1702;
              DCOMP.COMP.FromOwnership(r, _4481_fromOwnership, expectedOwnership, out _out1701, out _out1702);
              r = _out1701;
              resultingOwnership = _out1702;
              readIdents = _4479_recIdents;
            }
            return ;
          }
        } else if (_source177.is_BinOp) {
          DAST._IBinOp _4482___mcc_h133 = _source177.dtor_op;
          DAST._IExpression _4483___mcc_h134 = _source177.dtor_left;
          DAST._IExpression _4484___mcc_h135 = _source177.dtor_right;
          DAST.Format._IBinaryOpFormat _4485___mcc_h136 = _source177.dtor_format2;
          DAST._IType _4486_fieldType = _4153___mcc_h52;
          bool _4487_isDatatype = _4152___mcc_h51;
          bool _4488_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4489_field = _4150___mcc_h49;
          DAST._IExpression _4490_on = _4149___mcc_h48;
          {
            if (_4487_isDatatype) {
              RAST._IExpr _4491_onExpr;
              DCOMP._IOwnership _4492_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4493_recIdents;
              RAST._IExpr _out1703;
              DCOMP._IOwnership _out1704;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1705;
              (this).GenExpr(_4490_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1703, out _out1704, out _out1705);
              _4491_onExpr = _out1703;
              _4492_onOwned = _out1704;
              _4493_recIdents = _out1705;
              r = ((_4491_onExpr).Sel(DCOMP.__default.escapeName(_4489_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4494_typ;
              RAST._IType _out1706;
              _out1706 = (this).GenType(_4486_fieldType, false, false);
              _4494_typ = _out1706;
              if (((_4494_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1707;
                DCOMP._IOwnership _out1708;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1707, out _out1708);
                r = _out1707;
                resultingOwnership = _out1708;
              }
              readIdents = _4493_recIdents;
            } else {
              RAST._IExpr _4495_onExpr;
              DCOMP._IOwnership _4496_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4497_recIdents;
              RAST._IExpr _out1709;
              DCOMP._IOwnership _out1710;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1711;
              (this).GenExpr(_4490_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1709, out _out1710, out _out1711);
              _4495_onExpr = _out1709;
              _4496_onOwned = _out1710;
              _4497_recIdents = _out1711;
              r = _4495_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4489_field));
              if (_4488_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4498_s;
                _4498_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4495_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4489_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4498_s);
              }
              DCOMP._IOwnership _4499_fromOwnership;
              _4499_fromOwnership = ((_4488_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1712;
              DCOMP._IOwnership _out1713;
              DCOMP.COMP.FromOwnership(r, _4499_fromOwnership, expectedOwnership, out _out1712, out _out1713);
              r = _out1712;
              resultingOwnership = _out1713;
              readIdents = _4497_recIdents;
            }
            return ;
          }
        } else if (_source177.is_ArrayLen) {
          DAST._IExpression _4500___mcc_h141 = _source177.dtor_expr;
          BigInteger _4501___mcc_h142 = _source177.dtor_dim;
          DAST._IType _4502_fieldType = _4153___mcc_h52;
          bool _4503_isDatatype = _4152___mcc_h51;
          bool _4504_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4505_field = _4150___mcc_h49;
          DAST._IExpression _4506_on = _4149___mcc_h48;
          {
            if (_4503_isDatatype) {
              RAST._IExpr _4507_onExpr;
              DCOMP._IOwnership _4508_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4509_recIdents;
              RAST._IExpr _out1714;
              DCOMP._IOwnership _out1715;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1716;
              (this).GenExpr(_4506_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1714, out _out1715, out _out1716);
              _4507_onExpr = _out1714;
              _4508_onOwned = _out1715;
              _4509_recIdents = _out1716;
              r = ((_4507_onExpr).Sel(DCOMP.__default.escapeName(_4505_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4510_typ;
              RAST._IType _out1717;
              _out1717 = (this).GenType(_4502_fieldType, false, false);
              _4510_typ = _out1717;
              if (((_4510_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1718;
                DCOMP._IOwnership _out1719;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1718, out _out1719);
                r = _out1718;
                resultingOwnership = _out1719;
              }
              readIdents = _4509_recIdents;
            } else {
              RAST._IExpr _4511_onExpr;
              DCOMP._IOwnership _4512_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4513_recIdents;
              RAST._IExpr _out1720;
              DCOMP._IOwnership _out1721;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1722;
              (this).GenExpr(_4506_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1720, out _out1721, out _out1722);
              _4511_onExpr = _out1720;
              _4512_onOwned = _out1721;
              _4513_recIdents = _out1722;
              r = _4511_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4505_field));
              if (_4504_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4514_s;
                _4514_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4511_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4505_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4514_s);
              }
              DCOMP._IOwnership _4515_fromOwnership;
              _4515_fromOwnership = ((_4504_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1723;
              DCOMP._IOwnership _out1724;
              DCOMP.COMP.FromOwnership(r, _4515_fromOwnership, expectedOwnership, out _out1723, out _out1724);
              r = _out1723;
              resultingOwnership = _out1724;
              readIdents = _4513_recIdents;
            }
            return ;
          }
        } else if (_source177.is_MapKeys) {
          DAST._IExpression _4516___mcc_h145 = _source177.dtor_expr;
          DAST._IType _4517_fieldType = _4153___mcc_h52;
          bool _4518_isDatatype = _4152___mcc_h51;
          bool _4519_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4520_field = _4150___mcc_h49;
          DAST._IExpression _4521_on = _4149___mcc_h48;
          {
            if (_4518_isDatatype) {
              RAST._IExpr _4522_onExpr;
              DCOMP._IOwnership _4523_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4524_recIdents;
              RAST._IExpr _out1725;
              DCOMP._IOwnership _out1726;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1727;
              (this).GenExpr(_4521_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1725, out _out1726, out _out1727);
              _4522_onExpr = _out1725;
              _4523_onOwned = _out1726;
              _4524_recIdents = _out1727;
              r = ((_4522_onExpr).Sel(DCOMP.__default.escapeName(_4520_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4525_typ;
              RAST._IType _out1728;
              _out1728 = (this).GenType(_4517_fieldType, false, false);
              _4525_typ = _out1728;
              if (((_4525_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1729;
                DCOMP._IOwnership _out1730;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1729, out _out1730);
                r = _out1729;
                resultingOwnership = _out1730;
              }
              readIdents = _4524_recIdents;
            } else {
              RAST._IExpr _4526_onExpr;
              DCOMP._IOwnership _4527_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4528_recIdents;
              RAST._IExpr _out1731;
              DCOMP._IOwnership _out1732;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1733;
              (this).GenExpr(_4521_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1731, out _out1732, out _out1733);
              _4526_onExpr = _out1731;
              _4527_onOwned = _out1732;
              _4528_recIdents = _out1733;
              r = _4526_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4520_field));
              if (_4519_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4529_s;
                _4529_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4526_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4520_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4529_s);
              }
              DCOMP._IOwnership _4530_fromOwnership;
              _4530_fromOwnership = ((_4519_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1734;
              DCOMP._IOwnership _out1735;
              DCOMP.COMP.FromOwnership(r, _4530_fromOwnership, expectedOwnership, out _out1734, out _out1735);
              r = _out1734;
              resultingOwnership = _out1735;
              readIdents = _4528_recIdents;
            }
            return ;
          }
        } else if (_source177.is_MapValues) {
          DAST._IExpression _4531___mcc_h147 = _source177.dtor_expr;
          DAST._IType _4532_fieldType = _4153___mcc_h52;
          bool _4533_isDatatype = _4152___mcc_h51;
          bool _4534_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4535_field = _4150___mcc_h49;
          DAST._IExpression _4536_on = _4149___mcc_h48;
          {
            if (_4533_isDatatype) {
              RAST._IExpr _4537_onExpr;
              DCOMP._IOwnership _4538_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4539_recIdents;
              RAST._IExpr _out1736;
              DCOMP._IOwnership _out1737;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1738;
              (this).GenExpr(_4536_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1736, out _out1737, out _out1738);
              _4537_onExpr = _out1736;
              _4538_onOwned = _out1737;
              _4539_recIdents = _out1738;
              r = ((_4537_onExpr).Sel(DCOMP.__default.escapeName(_4535_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4540_typ;
              RAST._IType _out1739;
              _out1739 = (this).GenType(_4532_fieldType, false, false);
              _4540_typ = _out1739;
              if (((_4540_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1740;
                DCOMP._IOwnership _out1741;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1740, out _out1741);
                r = _out1740;
                resultingOwnership = _out1741;
              }
              readIdents = _4539_recIdents;
            } else {
              RAST._IExpr _4541_onExpr;
              DCOMP._IOwnership _4542_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4543_recIdents;
              RAST._IExpr _out1742;
              DCOMP._IOwnership _out1743;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1744;
              (this).GenExpr(_4536_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1742, out _out1743, out _out1744);
              _4541_onExpr = _out1742;
              _4542_onOwned = _out1743;
              _4543_recIdents = _out1744;
              r = _4541_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4535_field));
              if (_4534_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4544_s;
                _4544_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4541_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4535_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4544_s);
              }
              DCOMP._IOwnership _4545_fromOwnership;
              _4545_fromOwnership = ((_4534_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1745;
              DCOMP._IOwnership _out1746;
              DCOMP.COMP.FromOwnership(r, _4545_fromOwnership, expectedOwnership, out _out1745, out _out1746);
              r = _out1745;
              resultingOwnership = _out1746;
              readIdents = _4543_recIdents;
            }
            return ;
          }
        } else if (_source177.is_Select) {
          DAST._IExpression _4546___mcc_h149 = _source177.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _4547___mcc_h150 = _source177.dtor_field;
          bool _4548___mcc_h151 = _source177.dtor_isConstant;
          bool _4549___mcc_h152 = _source177.dtor_onDatatype;
          DAST._IType _4550___mcc_h153 = _source177.dtor_fieldType;
          DAST._IType _4551_fieldType = _4153___mcc_h52;
          bool _4552_isDatatype = _4152___mcc_h51;
          bool _4553_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4554_field = _4150___mcc_h49;
          DAST._IExpression _4555_on = _4149___mcc_h48;
          {
            if (_4552_isDatatype) {
              RAST._IExpr _4556_onExpr;
              DCOMP._IOwnership _4557_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4558_recIdents;
              RAST._IExpr _out1747;
              DCOMP._IOwnership _out1748;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1749;
              (this).GenExpr(_4555_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1747, out _out1748, out _out1749);
              _4556_onExpr = _out1747;
              _4557_onOwned = _out1748;
              _4558_recIdents = _out1749;
              r = ((_4556_onExpr).Sel(DCOMP.__default.escapeName(_4554_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4559_typ;
              RAST._IType _out1750;
              _out1750 = (this).GenType(_4551_fieldType, false, false);
              _4559_typ = _out1750;
              if (((_4559_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1751;
                DCOMP._IOwnership _out1752;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1751, out _out1752);
                r = _out1751;
                resultingOwnership = _out1752;
              }
              readIdents = _4558_recIdents;
            } else {
              RAST._IExpr _4560_onExpr;
              DCOMP._IOwnership _4561_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4562_recIdents;
              RAST._IExpr _out1753;
              DCOMP._IOwnership _out1754;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1755;
              (this).GenExpr(_4555_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1753, out _out1754, out _out1755);
              _4560_onExpr = _out1753;
              _4561_onOwned = _out1754;
              _4562_recIdents = _out1755;
              r = _4560_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4554_field));
              if (_4553_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4563_s;
                _4563_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4560_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4554_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4563_s);
              }
              DCOMP._IOwnership _4564_fromOwnership;
              _4564_fromOwnership = ((_4553_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1756;
              DCOMP._IOwnership _out1757;
              DCOMP.COMP.FromOwnership(r, _4564_fromOwnership, expectedOwnership, out _out1756, out _out1757);
              r = _out1756;
              resultingOwnership = _out1757;
              readIdents = _4562_recIdents;
            }
            return ;
          }
        } else if (_source177.is_SelectFn) {
          DAST._IExpression _4565___mcc_h159 = _source177.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _4566___mcc_h160 = _source177.dtor_field;
          bool _4567___mcc_h161 = _source177.dtor_onDatatype;
          bool _4568___mcc_h162 = _source177.dtor_isStatic;
          BigInteger _4569___mcc_h163 = _source177.dtor_arity;
          DAST._IType _4570_fieldType = _4153___mcc_h52;
          bool _4571_isDatatype = _4152___mcc_h51;
          bool _4572_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4573_field = _4150___mcc_h49;
          DAST._IExpression _4574_on = _4149___mcc_h48;
          {
            if (_4571_isDatatype) {
              RAST._IExpr _4575_onExpr;
              DCOMP._IOwnership _4576_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4577_recIdents;
              RAST._IExpr _out1758;
              DCOMP._IOwnership _out1759;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1760;
              (this).GenExpr(_4574_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1758, out _out1759, out _out1760);
              _4575_onExpr = _out1758;
              _4576_onOwned = _out1759;
              _4577_recIdents = _out1760;
              r = ((_4575_onExpr).Sel(DCOMP.__default.escapeName(_4573_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4578_typ;
              RAST._IType _out1761;
              _out1761 = (this).GenType(_4570_fieldType, false, false);
              _4578_typ = _out1761;
              if (((_4578_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1762;
                DCOMP._IOwnership _out1763;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1762, out _out1763);
                r = _out1762;
                resultingOwnership = _out1763;
              }
              readIdents = _4577_recIdents;
            } else {
              RAST._IExpr _4579_onExpr;
              DCOMP._IOwnership _4580_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4581_recIdents;
              RAST._IExpr _out1764;
              DCOMP._IOwnership _out1765;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1766;
              (this).GenExpr(_4574_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1764, out _out1765, out _out1766);
              _4579_onExpr = _out1764;
              _4580_onOwned = _out1765;
              _4581_recIdents = _out1766;
              r = _4579_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4573_field));
              if (_4572_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4582_s;
                _4582_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4579_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4573_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4582_s);
              }
              DCOMP._IOwnership _4583_fromOwnership;
              _4583_fromOwnership = ((_4572_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1767;
              DCOMP._IOwnership _out1768;
              DCOMP.COMP.FromOwnership(r, _4583_fromOwnership, expectedOwnership, out _out1767, out _out1768);
              r = _out1767;
              resultingOwnership = _out1768;
              readIdents = _4581_recIdents;
            }
            return ;
          }
        } else if (_source177.is_Index) {
          DAST._IExpression _4584___mcc_h169 = _source177.dtor_expr;
          DAST._ICollKind _4585___mcc_h170 = _source177.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _4586___mcc_h171 = _source177.dtor_indices;
          DAST._IType _4587_fieldType = _4153___mcc_h52;
          bool _4588_isDatatype = _4152___mcc_h51;
          bool _4589_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4590_field = _4150___mcc_h49;
          DAST._IExpression _4591_on = _4149___mcc_h48;
          {
            if (_4588_isDatatype) {
              RAST._IExpr _4592_onExpr;
              DCOMP._IOwnership _4593_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4594_recIdents;
              RAST._IExpr _out1769;
              DCOMP._IOwnership _out1770;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1771;
              (this).GenExpr(_4591_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1769, out _out1770, out _out1771);
              _4592_onExpr = _out1769;
              _4593_onOwned = _out1770;
              _4594_recIdents = _out1771;
              r = ((_4592_onExpr).Sel(DCOMP.__default.escapeName(_4590_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4595_typ;
              RAST._IType _out1772;
              _out1772 = (this).GenType(_4587_fieldType, false, false);
              _4595_typ = _out1772;
              if (((_4595_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1773;
                DCOMP._IOwnership _out1774;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1773, out _out1774);
                r = _out1773;
                resultingOwnership = _out1774;
              }
              readIdents = _4594_recIdents;
            } else {
              RAST._IExpr _4596_onExpr;
              DCOMP._IOwnership _4597_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4598_recIdents;
              RAST._IExpr _out1775;
              DCOMP._IOwnership _out1776;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1777;
              (this).GenExpr(_4591_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1775, out _out1776, out _out1777);
              _4596_onExpr = _out1775;
              _4597_onOwned = _out1776;
              _4598_recIdents = _out1777;
              r = _4596_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4590_field));
              if (_4589_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4599_s;
                _4599_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4596_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4590_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4599_s);
              }
              DCOMP._IOwnership _4600_fromOwnership;
              _4600_fromOwnership = ((_4589_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1778;
              DCOMP._IOwnership _out1779;
              DCOMP.COMP.FromOwnership(r, _4600_fromOwnership, expectedOwnership, out _out1778, out _out1779);
              r = _out1778;
              resultingOwnership = _out1779;
              readIdents = _4598_recIdents;
            }
            return ;
          }
        } else if (_source177.is_IndexRange) {
          DAST._IExpression _4601___mcc_h175 = _source177.dtor_expr;
          bool _4602___mcc_h176 = _source177.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _4603___mcc_h177 = _source177.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _4604___mcc_h178 = _source177.dtor_high;
          DAST._IType _4605_fieldType = _4153___mcc_h52;
          bool _4606_isDatatype = _4152___mcc_h51;
          bool _4607_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4608_field = _4150___mcc_h49;
          DAST._IExpression _4609_on = _4149___mcc_h48;
          {
            if (_4606_isDatatype) {
              RAST._IExpr _4610_onExpr;
              DCOMP._IOwnership _4611_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4612_recIdents;
              RAST._IExpr _out1780;
              DCOMP._IOwnership _out1781;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1782;
              (this).GenExpr(_4609_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1780, out _out1781, out _out1782);
              _4610_onExpr = _out1780;
              _4611_onOwned = _out1781;
              _4612_recIdents = _out1782;
              r = ((_4610_onExpr).Sel(DCOMP.__default.escapeName(_4608_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4613_typ;
              RAST._IType _out1783;
              _out1783 = (this).GenType(_4605_fieldType, false, false);
              _4613_typ = _out1783;
              if (((_4613_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1784;
                DCOMP._IOwnership _out1785;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1784, out _out1785);
                r = _out1784;
                resultingOwnership = _out1785;
              }
              readIdents = _4612_recIdents;
            } else {
              RAST._IExpr _4614_onExpr;
              DCOMP._IOwnership _4615_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4616_recIdents;
              RAST._IExpr _out1786;
              DCOMP._IOwnership _out1787;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1788;
              (this).GenExpr(_4609_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1786, out _out1787, out _out1788);
              _4614_onExpr = _out1786;
              _4615_onOwned = _out1787;
              _4616_recIdents = _out1788;
              r = _4614_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4608_field));
              if (_4607_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4617_s;
                _4617_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4614_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4608_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4617_s);
              }
              DCOMP._IOwnership _4618_fromOwnership;
              _4618_fromOwnership = ((_4607_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1789;
              DCOMP._IOwnership _out1790;
              DCOMP.COMP.FromOwnership(r, _4618_fromOwnership, expectedOwnership, out _out1789, out _out1790);
              r = _out1789;
              resultingOwnership = _out1790;
              readIdents = _4616_recIdents;
            }
            return ;
          }
        } else if (_source177.is_TupleSelect) {
          DAST._IExpression _4619___mcc_h183 = _source177.dtor_expr;
          BigInteger _4620___mcc_h184 = _source177.dtor_index;
          DAST._IType _4621___mcc_h185 = _source177.dtor_fieldType;
          DAST._IType _4622_fieldType = _4153___mcc_h52;
          bool _4623_isDatatype = _4152___mcc_h51;
          bool _4624_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4625_field = _4150___mcc_h49;
          DAST._IExpression _4626_on = _4149___mcc_h48;
          {
            if (_4623_isDatatype) {
              RAST._IExpr _4627_onExpr;
              DCOMP._IOwnership _4628_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4629_recIdents;
              RAST._IExpr _out1791;
              DCOMP._IOwnership _out1792;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1793;
              (this).GenExpr(_4626_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1791, out _out1792, out _out1793);
              _4627_onExpr = _out1791;
              _4628_onOwned = _out1792;
              _4629_recIdents = _out1793;
              r = ((_4627_onExpr).Sel(DCOMP.__default.escapeName(_4625_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4630_typ;
              RAST._IType _out1794;
              _out1794 = (this).GenType(_4622_fieldType, false, false);
              _4630_typ = _out1794;
              if (((_4630_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1795;
                DCOMP._IOwnership _out1796;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1795, out _out1796);
                r = _out1795;
                resultingOwnership = _out1796;
              }
              readIdents = _4629_recIdents;
            } else {
              RAST._IExpr _4631_onExpr;
              DCOMP._IOwnership _4632_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4633_recIdents;
              RAST._IExpr _out1797;
              DCOMP._IOwnership _out1798;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1799;
              (this).GenExpr(_4626_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1797, out _out1798, out _out1799);
              _4631_onExpr = _out1797;
              _4632_onOwned = _out1798;
              _4633_recIdents = _out1799;
              r = _4631_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4625_field));
              if (_4624_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4634_s;
                _4634_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4631_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4625_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4634_s);
              }
              DCOMP._IOwnership _4635_fromOwnership;
              _4635_fromOwnership = ((_4624_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1800;
              DCOMP._IOwnership _out1801;
              DCOMP.COMP.FromOwnership(r, _4635_fromOwnership, expectedOwnership, out _out1800, out _out1801);
              r = _out1800;
              resultingOwnership = _out1801;
              readIdents = _4633_recIdents;
            }
            return ;
          }
        } else if (_source177.is_Call) {
          DAST._IExpression _4636___mcc_h189 = _source177.dtor_on;
          DAST._ICallName _4637___mcc_h190 = _source177.dtor_callName;
          Dafny.ISequence<DAST._IType> _4638___mcc_h191 = _source177.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _4639___mcc_h192 = _source177.dtor_args;
          DAST._IType _4640_fieldType = _4153___mcc_h52;
          bool _4641_isDatatype = _4152___mcc_h51;
          bool _4642_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4643_field = _4150___mcc_h49;
          DAST._IExpression _4644_on = _4149___mcc_h48;
          {
            if (_4641_isDatatype) {
              RAST._IExpr _4645_onExpr;
              DCOMP._IOwnership _4646_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4647_recIdents;
              RAST._IExpr _out1802;
              DCOMP._IOwnership _out1803;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1804;
              (this).GenExpr(_4644_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1802, out _out1803, out _out1804);
              _4645_onExpr = _out1802;
              _4646_onOwned = _out1803;
              _4647_recIdents = _out1804;
              r = ((_4645_onExpr).Sel(DCOMP.__default.escapeName(_4643_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4648_typ;
              RAST._IType _out1805;
              _out1805 = (this).GenType(_4640_fieldType, false, false);
              _4648_typ = _out1805;
              if (((_4648_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1806;
                DCOMP._IOwnership _out1807;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1806, out _out1807);
                r = _out1806;
                resultingOwnership = _out1807;
              }
              readIdents = _4647_recIdents;
            } else {
              RAST._IExpr _4649_onExpr;
              DCOMP._IOwnership _4650_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4651_recIdents;
              RAST._IExpr _out1808;
              DCOMP._IOwnership _out1809;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1810;
              (this).GenExpr(_4644_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1808, out _out1809, out _out1810);
              _4649_onExpr = _out1808;
              _4650_onOwned = _out1809;
              _4651_recIdents = _out1810;
              r = _4649_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4643_field));
              if (_4642_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4652_s;
                _4652_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4649_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4643_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4652_s);
              }
              DCOMP._IOwnership _4653_fromOwnership;
              _4653_fromOwnership = ((_4642_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1811;
              DCOMP._IOwnership _out1812;
              DCOMP.COMP.FromOwnership(r, _4653_fromOwnership, expectedOwnership, out _out1811, out _out1812);
              r = _out1811;
              resultingOwnership = _out1812;
              readIdents = _4651_recIdents;
            }
            return ;
          }
        } else if (_source177.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _4654___mcc_h197 = _source177.dtor_params;
          DAST._IType _4655___mcc_h198 = _source177.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _4656___mcc_h199 = _source177.dtor_body;
          DAST._IType _4657_fieldType = _4153___mcc_h52;
          bool _4658_isDatatype = _4152___mcc_h51;
          bool _4659_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4660_field = _4150___mcc_h49;
          DAST._IExpression _4661_on = _4149___mcc_h48;
          {
            if (_4658_isDatatype) {
              RAST._IExpr _4662_onExpr;
              DCOMP._IOwnership _4663_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4664_recIdents;
              RAST._IExpr _out1813;
              DCOMP._IOwnership _out1814;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1815;
              (this).GenExpr(_4661_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1813, out _out1814, out _out1815);
              _4662_onExpr = _out1813;
              _4663_onOwned = _out1814;
              _4664_recIdents = _out1815;
              r = ((_4662_onExpr).Sel(DCOMP.__default.escapeName(_4660_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4665_typ;
              RAST._IType _out1816;
              _out1816 = (this).GenType(_4657_fieldType, false, false);
              _4665_typ = _out1816;
              if (((_4665_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1817;
                DCOMP._IOwnership _out1818;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1817, out _out1818);
                r = _out1817;
                resultingOwnership = _out1818;
              }
              readIdents = _4664_recIdents;
            } else {
              RAST._IExpr _4666_onExpr;
              DCOMP._IOwnership _4667_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4668_recIdents;
              RAST._IExpr _out1819;
              DCOMP._IOwnership _out1820;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1821;
              (this).GenExpr(_4661_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1819, out _out1820, out _out1821);
              _4666_onExpr = _out1819;
              _4667_onOwned = _out1820;
              _4668_recIdents = _out1821;
              r = _4666_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4660_field));
              if (_4659_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4669_s;
                _4669_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4666_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4660_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4669_s);
              }
              DCOMP._IOwnership _4670_fromOwnership;
              _4670_fromOwnership = ((_4659_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1822;
              DCOMP._IOwnership _out1823;
              DCOMP.COMP.FromOwnership(r, _4670_fromOwnership, expectedOwnership, out _out1822, out _out1823);
              r = _out1822;
              resultingOwnership = _out1823;
              readIdents = _4668_recIdents;
            }
            return ;
          }
        } else if (_source177.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _4671___mcc_h203 = _source177.dtor_values;
          DAST._IType _4672___mcc_h204 = _source177.dtor_retType;
          DAST._IExpression _4673___mcc_h205 = _source177.dtor_expr;
          DAST._IType _4674_fieldType = _4153___mcc_h52;
          bool _4675_isDatatype = _4152___mcc_h51;
          bool _4676_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4677_field = _4150___mcc_h49;
          DAST._IExpression _4678_on = _4149___mcc_h48;
          {
            if (_4675_isDatatype) {
              RAST._IExpr _4679_onExpr;
              DCOMP._IOwnership _4680_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4681_recIdents;
              RAST._IExpr _out1824;
              DCOMP._IOwnership _out1825;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1826;
              (this).GenExpr(_4678_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1824, out _out1825, out _out1826);
              _4679_onExpr = _out1824;
              _4680_onOwned = _out1825;
              _4681_recIdents = _out1826;
              r = ((_4679_onExpr).Sel(DCOMP.__default.escapeName(_4677_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4682_typ;
              RAST._IType _out1827;
              _out1827 = (this).GenType(_4674_fieldType, false, false);
              _4682_typ = _out1827;
              if (((_4682_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1828;
                DCOMP._IOwnership _out1829;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1828, out _out1829);
                r = _out1828;
                resultingOwnership = _out1829;
              }
              readIdents = _4681_recIdents;
            } else {
              RAST._IExpr _4683_onExpr;
              DCOMP._IOwnership _4684_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4685_recIdents;
              RAST._IExpr _out1830;
              DCOMP._IOwnership _out1831;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1832;
              (this).GenExpr(_4678_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1830, out _out1831, out _out1832);
              _4683_onExpr = _out1830;
              _4684_onOwned = _out1831;
              _4685_recIdents = _out1832;
              r = _4683_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4677_field));
              if (_4676_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4686_s;
                _4686_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4683_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4677_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4686_s);
              }
              DCOMP._IOwnership _4687_fromOwnership;
              _4687_fromOwnership = ((_4676_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1833;
              DCOMP._IOwnership _out1834;
              DCOMP.COMP.FromOwnership(r, _4687_fromOwnership, expectedOwnership, out _out1833, out _out1834);
              r = _out1833;
              resultingOwnership = _out1834;
              readIdents = _4685_recIdents;
            }
            return ;
          }
        } else if (_source177.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _4688___mcc_h209 = _source177.dtor_name;
          DAST._IType _4689___mcc_h210 = _source177.dtor_typ;
          DAST._IExpression _4690___mcc_h211 = _source177.dtor_value;
          DAST._IExpression _4691___mcc_h212 = _source177.dtor_iifeBody;
          DAST._IType _4692_fieldType = _4153___mcc_h52;
          bool _4693_isDatatype = _4152___mcc_h51;
          bool _4694_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4695_field = _4150___mcc_h49;
          DAST._IExpression _4696_on = _4149___mcc_h48;
          {
            if (_4693_isDatatype) {
              RAST._IExpr _4697_onExpr;
              DCOMP._IOwnership _4698_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4699_recIdents;
              RAST._IExpr _out1835;
              DCOMP._IOwnership _out1836;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1837;
              (this).GenExpr(_4696_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1835, out _out1836, out _out1837);
              _4697_onExpr = _out1835;
              _4698_onOwned = _out1836;
              _4699_recIdents = _out1837;
              r = ((_4697_onExpr).Sel(DCOMP.__default.escapeName(_4695_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4700_typ;
              RAST._IType _out1838;
              _out1838 = (this).GenType(_4692_fieldType, false, false);
              _4700_typ = _out1838;
              if (((_4700_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1839;
                DCOMP._IOwnership _out1840;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1839, out _out1840);
                r = _out1839;
                resultingOwnership = _out1840;
              }
              readIdents = _4699_recIdents;
            } else {
              RAST._IExpr _4701_onExpr;
              DCOMP._IOwnership _4702_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4703_recIdents;
              RAST._IExpr _out1841;
              DCOMP._IOwnership _out1842;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1843;
              (this).GenExpr(_4696_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1841, out _out1842, out _out1843);
              _4701_onExpr = _out1841;
              _4702_onOwned = _out1842;
              _4703_recIdents = _out1843;
              r = _4701_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4695_field));
              if (_4694_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4704_s;
                _4704_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4701_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4695_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4704_s);
              }
              DCOMP._IOwnership _4705_fromOwnership;
              _4705_fromOwnership = ((_4694_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1844;
              DCOMP._IOwnership _out1845;
              DCOMP.COMP.FromOwnership(r, _4705_fromOwnership, expectedOwnership, out _out1844, out _out1845);
              r = _out1844;
              resultingOwnership = _out1845;
              readIdents = _4703_recIdents;
            }
            return ;
          }
        } else if (_source177.is_Apply) {
          DAST._IExpression _4706___mcc_h217 = _source177.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _4707___mcc_h218 = _source177.dtor_args;
          DAST._IType _4708_fieldType = _4153___mcc_h52;
          bool _4709_isDatatype = _4152___mcc_h51;
          bool _4710_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4711_field = _4150___mcc_h49;
          DAST._IExpression _4712_on = _4149___mcc_h48;
          {
            if (_4709_isDatatype) {
              RAST._IExpr _4713_onExpr;
              DCOMP._IOwnership _4714_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4715_recIdents;
              RAST._IExpr _out1846;
              DCOMP._IOwnership _out1847;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1848;
              (this).GenExpr(_4712_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1846, out _out1847, out _out1848);
              _4713_onExpr = _out1846;
              _4714_onOwned = _out1847;
              _4715_recIdents = _out1848;
              r = ((_4713_onExpr).Sel(DCOMP.__default.escapeName(_4711_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4716_typ;
              RAST._IType _out1849;
              _out1849 = (this).GenType(_4708_fieldType, false, false);
              _4716_typ = _out1849;
              if (((_4716_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1850;
                DCOMP._IOwnership _out1851;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1850, out _out1851);
                r = _out1850;
                resultingOwnership = _out1851;
              }
              readIdents = _4715_recIdents;
            } else {
              RAST._IExpr _4717_onExpr;
              DCOMP._IOwnership _4718_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4719_recIdents;
              RAST._IExpr _out1852;
              DCOMP._IOwnership _out1853;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1854;
              (this).GenExpr(_4712_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1852, out _out1853, out _out1854);
              _4717_onExpr = _out1852;
              _4718_onOwned = _out1853;
              _4719_recIdents = _out1854;
              r = _4717_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4711_field));
              if (_4710_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4720_s;
                _4720_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4717_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4711_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4720_s);
              }
              DCOMP._IOwnership _4721_fromOwnership;
              _4721_fromOwnership = ((_4710_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1855;
              DCOMP._IOwnership _out1856;
              DCOMP.COMP.FromOwnership(r, _4721_fromOwnership, expectedOwnership, out _out1855, out _out1856);
              r = _out1855;
              resultingOwnership = _out1856;
              readIdents = _4719_recIdents;
            }
            return ;
          }
        } else if (_source177.is_TypeTest) {
          DAST._IExpression _4722___mcc_h221 = _source177.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4723___mcc_h222 = _source177.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _4724___mcc_h223 = _source177.dtor_variant;
          DAST._IType _4725_fieldType = _4153___mcc_h52;
          bool _4726_isDatatype = _4152___mcc_h51;
          bool _4727_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4728_field = _4150___mcc_h49;
          DAST._IExpression _4729_on = _4149___mcc_h48;
          {
            if (_4726_isDatatype) {
              RAST._IExpr _4730_onExpr;
              DCOMP._IOwnership _4731_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4732_recIdents;
              RAST._IExpr _out1857;
              DCOMP._IOwnership _out1858;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1859;
              (this).GenExpr(_4729_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1857, out _out1858, out _out1859);
              _4730_onExpr = _out1857;
              _4731_onOwned = _out1858;
              _4732_recIdents = _out1859;
              r = ((_4730_onExpr).Sel(DCOMP.__default.escapeName(_4728_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4733_typ;
              RAST._IType _out1860;
              _out1860 = (this).GenType(_4725_fieldType, false, false);
              _4733_typ = _out1860;
              if (((_4733_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1861;
                DCOMP._IOwnership _out1862;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1861, out _out1862);
                r = _out1861;
                resultingOwnership = _out1862;
              }
              readIdents = _4732_recIdents;
            } else {
              RAST._IExpr _4734_onExpr;
              DCOMP._IOwnership _4735_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4736_recIdents;
              RAST._IExpr _out1863;
              DCOMP._IOwnership _out1864;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1865;
              (this).GenExpr(_4729_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1863, out _out1864, out _out1865);
              _4734_onExpr = _out1863;
              _4735_onOwned = _out1864;
              _4736_recIdents = _out1865;
              r = _4734_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4728_field));
              if (_4727_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4737_s;
                _4737_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4734_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4728_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4737_s);
              }
              DCOMP._IOwnership _4738_fromOwnership;
              _4738_fromOwnership = ((_4727_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1866;
              DCOMP._IOwnership _out1867;
              DCOMP.COMP.FromOwnership(r, _4738_fromOwnership, expectedOwnership, out _out1866, out _out1867);
              r = _out1866;
              resultingOwnership = _out1867;
              readIdents = _4736_recIdents;
            }
            return ;
          }
        } else if (_source177.is_InitializationValue) {
          DAST._IType _4739___mcc_h227 = _source177.dtor_typ;
          DAST._IType _4740_fieldType = _4153___mcc_h52;
          bool _4741_isDatatype = _4152___mcc_h51;
          bool _4742_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4743_field = _4150___mcc_h49;
          DAST._IExpression _4744_on = _4149___mcc_h48;
          {
            if (_4741_isDatatype) {
              RAST._IExpr _4745_onExpr;
              DCOMP._IOwnership _4746_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4747_recIdents;
              RAST._IExpr _out1868;
              DCOMP._IOwnership _out1869;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1870;
              (this).GenExpr(_4744_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1868, out _out1869, out _out1870);
              _4745_onExpr = _out1868;
              _4746_onOwned = _out1869;
              _4747_recIdents = _out1870;
              r = ((_4745_onExpr).Sel(DCOMP.__default.escapeName(_4743_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4748_typ;
              RAST._IType _out1871;
              _out1871 = (this).GenType(_4740_fieldType, false, false);
              _4748_typ = _out1871;
              if (((_4748_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1872;
                DCOMP._IOwnership _out1873;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1872, out _out1873);
                r = _out1872;
                resultingOwnership = _out1873;
              }
              readIdents = _4747_recIdents;
            } else {
              RAST._IExpr _4749_onExpr;
              DCOMP._IOwnership _4750_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4751_recIdents;
              RAST._IExpr _out1874;
              DCOMP._IOwnership _out1875;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1876;
              (this).GenExpr(_4744_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1874, out _out1875, out _out1876);
              _4749_onExpr = _out1874;
              _4750_onOwned = _out1875;
              _4751_recIdents = _out1876;
              r = _4749_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4743_field));
              if (_4742_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4752_s;
                _4752_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4749_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4743_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4752_s);
              }
              DCOMP._IOwnership _4753_fromOwnership;
              _4753_fromOwnership = ((_4742_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1877;
              DCOMP._IOwnership _out1878;
              DCOMP.COMP.FromOwnership(r, _4753_fromOwnership, expectedOwnership, out _out1877, out _out1878);
              r = _out1877;
              resultingOwnership = _out1878;
              readIdents = _4751_recIdents;
            }
            return ;
          }
        } else if (_source177.is_BoolBoundedPool) {
          DAST._IType _4754_fieldType = _4153___mcc_h52;
          bool _4755_isDatatype = _4152___mcc_h51;
          bool _4756_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4757_field = _4150___mcc_h49;
          DAST._IExpression _4758_on = _4149___mcc_h48;
          {
            if (_4755_isDatatype) {
              RAST._IExpr _4759_onExpr;
              DCOMP._IOwnership _4760_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4761_recIdents;
              RAST._IExpr _out1879;
              DCOMP._IOwnership _out1880;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1881;
              (this).GenExpr(_4758_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1879, out _out1880, out _out1881);
              _4759_onExpr = _out1879;
              _4760_onOwned = _out1880;
              _4761_recIdents = _out1881;
              r = ((_4759_onExpr).Sel(DCOMP.__default.escapeName(_4757_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4762_typ;
              RAST._IType _out1882;
              _out1882 = (this).GenType(_4754_fieldType, false, false);
              _4762_typ = _out1882;
              if (((_4762_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1883;
                DCOMP._IOwnership _out1884;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1883, out _out1884);
                r = _out1883;
                resultingOwnership = _out1884;
              }
              readIdents = _4761_recIdents;
            } else {
              RAST._IExpr _4763_onExpr;
              DCOMP._IOwnership _4764_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4765_recIdents;
              RAST._IExpr _out1885;
              DCOMP._IOwnership _out1886;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1887;
              (this).GenExpr(_4758_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1885, out _out1886, out _out1887);
              _4763_onExpr = _out1885;
              _4764_onOwned = _out1886;
              _4765_recIdents = _out1887;
              r = _4763_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4757_field));
              if (_4756_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4766_s;
                _4766_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4763_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4757_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4766_s);
              }
              DCOMP._IOwnership _4767_fromOwnership;
              _4767_fromOwnership = ((_4756_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1888;
              DCOMP._IOwnership _out1889;
              DCOMP.COMP.FromOwnership(r, _4767_fromOwnership, expectedOwnership, out _out1888, out _out1889);
              r = _out1888;
              resultingOwnership = _out1889;
              readIdents = _4765_recIdents;
            }
            return ;
          }
        } else if (_source177.is_SetBoundedPool) {
          DAST._IExpression _4768___mcc_h229 = _source177.dtor_of;
          DAST._IType _4769_fieldType = _4153___mcc_h52;
          bool _4770_isDatatype = _4152___mcc_h51;
          bool _4771_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4772_field = _4150___mcc_h49;
          DAST._IExpression _4773_on = _4149___mcc_h48;
          {
            if (_4770_isDatatype) {
              RAST._IExpr _4774_onExpr;
              DCOMP._IOwnership _4775_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4776_recIdents;
              RAST._IExpr _out1890;
              DCOMP._IOwnership _out1891;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1892;
              (this).GenExpr(_4773_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1890, out _out1891, out _out1892);
              _4774_onExpr = _out1890;
              _4775_onOwned = _out1891;
              _4776_recIdents = _out1892;
              r = ((_4774_onExpr).Sel(DCOMP.__default.escapeName(_4772_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4777_typ;
              RAST._IType _out1893;
              _out1893 = (this).GenType(_4769_fieldType, false, false);
              _4777_typ = _out1893;
              if (((_4777_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1894;
                DCOMP._IOwnership _out1895;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1894, out _out1895);
                r = _out1894;
                resultingOwnership = _out1895;
              }
              readIdents = _4776_recIdents;
            } else {
              RAST._IExpr _4778_onExpr;
              DCOMP._IOwnership _4779_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4780_recIdents;
              RAST._IExpr _out1896;
              DCOMP._IOwnership _out1897;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1898;
              (this).GenExpr(_4773_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1896, out _out1897, out _out1898);
              _4778_onExpr = _out1896;
              _4779_onOwned = _out1897;
              _4780_recIdents = _out1898;
              r = _4778_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4772_field));
              if (_4771_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4781_s;
                _4781_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4778_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4772_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4781_s);
              }
              DCOMP._IOwnership _4782_fromOwnership;
              _4782_fromOwnership = ((_4771_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1899;
              DCOMP._IOwnership _out1900;
              DCOMP.COMP.FromOwnership(r, _4782_fromOwnership, expectedOwnership, out _out1899, out _out1900);
              r = _out1899;
              resultingOwnership = _out1900;
              readIdents = _4780_recIdents;
            }
            return ;
          }
        } else if (_source177.is_SeqBoundedPool) {
          DAST._IExpression _4783___mcc_h231 = _source177.dtor_of;
          bool _4784___mcc_h232 = _source177.dtor_includeDuplicates;
          DAST._IType _4785_fieldType = _4153___mcc_h52;
          bool _4786_isDatatype = _4152___mcc_h51;
          bool _4787_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4788_field = _4150___mcc_h49;
          DAST._IExpression _4789_on = _4149___mcc_h48;
          {
            if (_4786_isDatatype) {
              RAST._IExpr _4790_onExpr;
              DCOMP._IOwnership _4791_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4792_recIdents;
              RAST._IExpr _out1901;
              DCOMP._IOwnership _out1902;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1903;
              (this).GenExpr(_4789_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1901, out _out1902, out _out1903);
              _4790_onExpr = _out1901;
              _4791_onOwned = _out1902;
              _4792_recIdents = _out1903;
              r = ((_4790_onExpr).Sel(DCOMP.__default.escapeName(_4788_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4793_typ;
              RAST._IType _out1904;
              _out1904 = (this).GenType(_4785_fieldType, false, false);
              _4793_typ = _out1904;
              if (((_4793_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1905;
                DCOMP._IOwnership _out1906;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1905, out _out1906);
                r = _out1905;
                resultingOwnership = _out1906;
              }
              readIdents = _4792_recIdents;
            } else {
              RAST._IExpr _4794_onExpr;
              DCOMP._IOwnership _4795_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4796_recIdents;
              RAST._IExpr _out1907;
              DCOMP._IOwnership _out1908;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1909;
              (this).GenExpr(_4789_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1907, out _out1908, out _out1909);
              _4794_onExpr = _out1907;
              _4795_onOwned = _out1908;
              _4796_recIdents = _out1909;
              r = _4794_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4788_field));
              if (_4787_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4797_s;
                _4797_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4794_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4788_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4797_s);
              }
              DCOMP._IOwnership _4798_fromOwnership;
              _4798_fromOwnership = ((_4787_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1910;
              DCOMP._IOwnership _out1911;
              DCOMP.COMP.FromOwnership(r, _4798_fromOwnership, expectedOwnership, out _out1910, out _out1911);
              r = _out1910;
              resultingOwnership = _out1911;
              readIdents = _4796_recIdents;
            }
            return ;
          }
        } else {
          DAST._IExpression _4799___mcc_h235 = _source177.dtor_lo;
          DAST._IExpression _4800___mcc_h236 = _source177.dtor_hi;
          DAST._IType _4801_fieldType = _4153___mcc_h52;
          bool _4802_isDatatype = _4152___mcc_h51;
          bool _4803_isConstant = _4151___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4804_field = _4150___mcc_h49;
          DAST._IExpression _4805_on = _4149___mcc_h48;
          {
            if (_4802_isDatatype) {
              RAST._IExpr _4806_onExpr;
              DCOMP._IOwnership _4807_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4808_recIdents;
              RAST._IExpr _out1912;
              DCOMP._IOwnership _out1913;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1914;
              (this).GenExpr(_4805_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1912, out _out1913, out _out1914);
              _4806_onExpr = _out1912;
              _4807_onOwned = _out1913;
              _4808_recIdents = _out1914;
              r = ((_4806_onExpr).Sel(DCOMP.__default.escapeName(_4804_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4809_typ;
              RAST._IType _out1915;
              _out1915 = (this).GenType(_4801_fieldType, false, false);
              _4809_typ = _out1915;
              if (((_4809_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1916;
                DCOMP._IOwnership _out1917;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1916, out _out1917);
                r = _out1916;
                resultingOwnership = _out1917;
              }
              readIdents = _4808_recIdents;
            } else {
              RAST._IExpr _4810_onExpr;
              DCOMP._IOwnership _4811_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4812_recIdents;
              RAST._IExpr _out1918;
              DCOMP._IOwnership _out1919;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1920;
              (this).GenExpr(_4805_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1918, out _out1919, out _out1920);
              _4810_onExpr = _out1918;
              _4811_onOwned = _out1919;
              _4812_recIdents = _out1920;
              r = _4810_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4804_field));
              if (_4803_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4813_s;
                _4813_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4810_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4804_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4813_s);
              }
              DCOMP._IOwnership _4814_fromOwnership;
              _4814_fromOwnership = ((_4803_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1921;
              DCOMP._IOwnership _out1922;
              DCOMP.COMP.FromOwnership(r, _4814_fromOwnership, expectedOwnership, out _out1921, out _out1922);
              r = _out1921;
              resultingOwnership = _out1922;
              readIdents = _4812_recIdents;
            }
            return ;
          }
        }
      } else if (_source174.is_SelectFn) {
        DAST._IExpression _4815___mcc_h239 = _source174.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _4816___mcc_h240 = _source174.dtor_field;
        bool _4817___mcc_h241 = _source174.dtor_onDatatype;
        bool _4818___mcc_h242 = _source174.dtor_isStatic;
        BigInteger _4819___mcc_h243 = _source174.dtor_arity;
        BigInteger _4820_arity = _4819___mcc_h243;
        bool _4821_isStatic = _4818___mcc_h242;
        bool _4822_isDatatype = _4817___mcc_h241;
        Dafny.ISequence<Dafny.Rune> _4823_field = _4816___mcc_h240;
        DAST._IExpression _4824_on = _4815___mcc_h239;
        {
          RAST._IExpr _4825_onExpr;
          DCOMP._IOwnership _4826_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4827_recIdents;
          RAST._IExpr _out1923;
          DCOMP._IOwnership _out1924;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1925;
          (this).GenExpr(_4824_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1923, out _out1924, out _out1925);
          _4825_onExpr = _out1923;
          _4826_onOwned = _out1924;
          _4827_recIdents = _out1925;
          Dafny.ISequence<Dafny.Rune> _4828_s = Dafny.Sequence<Dafny.Rune>.Empty;
          Dafny.ISequence<Dafny.Rune> _4829_onString;
          _4829_onString = (_4825_onExpr)._ToString(DCOMP.__default.IND);
          if (_4821_isStatic) {
            _4828_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4829_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_4823_field));
          } else {
            _4828_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
            _4828_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4828_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _4829_onString), ((object.Equals(_4826_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            Dafny.ISequence<Dafny.Rune> _4830_args;
            _4830_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            BigInteger _4831_i;
            _4831_i = BigInteger.Zero;
            while ((_4831_i) < (_4820_arity)) {
              if ((_4831_i).Sign == 1) {
                _4830_args = Dafny.Sequence<Dafny.Rune>.Concat(_4830_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _4830_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4830_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_4831_i));
              _4831_i = (_4831_i) + (BigInteger.One);
            }
            _4828_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4828_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _4830_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
            _4828_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4828_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_4823_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _4830_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
            _4828_s = Dafny.Sequence<Dafny.Rune>.Concat(_4828_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            _4828_s = Dafny.Sequence<Dafny.Rune>.Concat(_4828_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
          }
          Dafny.ISequence<Dafny.Rune> _4832_typeShape;
          _4832_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
          BigInteger _4833_i;
          _4833_i = BigInteger.Zero;
          while ((_4833_i) < (_4820_arity)) {
            if ((_4833_i).Sign == 1) {
              _4832_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_4832_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            _4832_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_4832_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
            _4833_i = (_4833_i) + (BigInteger.One);
          }
          _4832_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_4832_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
          _4828_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _4828_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _4832_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          r = RAST.Expr.create_RawExpr(_4828_s);
          RAST._IExpr _out1926;
          DCOMP._IOwnership _out1927;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1926, out _out1927);
          r = _out1926;
          resultingOwnership = _out1927;
          readIdents = _4827_recIdents;
          return ;
        }
      } else if (_source174.is_Index) {
        DAST._IExpression _4834___mcc_h244 = _source174.dtor_expr;
        DAST._ICollKind _4835___mcc_h245 = _source174.dtor_collKind;
        Dafny.ISequence<DAST._IExpression> _4836___mcc_h246 = _source174.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _4837_indices = _4836___mcc_h246;
        DAST._ICollKind _4838_collKind = _4835___mcc_h245;
        DAST._IExpression _4839_on = _4834___mcc_h244;
        {
          RAST._IExpr _4840_onExpr;
          DCOMP._IOwnership _4841_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4842_recIdents;
          RAST._IExpr _out1928;
          DCOMP._IOwnership _out1929;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1930;
          (this).GenExpr(_4839_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1928, out _out1929, out _out1930);
          _4840_onExpr = _out1928;
          _4841_onOwned = _out1929;
          _4842_recIdents = _out1930;
          readIdents = _4842_recIdents;
          r = _4840_onExpr;
          BigInteger _4843_i;
          _4843_i = BigInteger.Zero;
          while ((_4843_i) < (new BigInteger((_4837_indices).Count))) {
            if (object.Equals(_4838_collKind, DAST.CollKind.create_Array())) {
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IExpr _4844_idx;
            DCOMP._IOwnership _4845_idxOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4846_recIdentsIdx;
            RAST._IExpr _out1931;
            DCOMP._IOwnership _out1932;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1933;
            (this).GenExpr((_4837_indices).Select(_4843_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1931, out _out1932, out _out1933);
            _4844_idx = _out1931;
            _4845_idxOwned = _out1932;
            _4846_recIdentsIdx = _out1933;
            r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_4844_idx);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4846_recIdentsIdx);
            _4843_i = (_4843_i) + (BigInteger.One);
          }
          RAST._IExpr _out1934;
          DCOMP._IOwnership _out1935;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1934, out _out1935);
          r = _out1934;
          resultingOwnership = _out1935;
          return ;
        }
      } else if (_source174.is_IndexRange) {
        DAST._IExpression _4847___mcc_h247 = _source174.dtor_expr;
        bool _4848___mcc_h248 = _source174.dtor_isArray;
        Std.Wrappers._IOption<DAST._IExpression> _4849___mcc_h249 = _source174.dtor_low;
        Std.Wrappers._IOption<DAST._IExpression> _4850___mcc_h250 = _source174.dtor_high;
        Std.Wrappers._IOption<DAST._IExpression> _4851_high = _4850___mcc_h250;
        Std.Wrappers._IOption<DAST._IExpression> _4852_low = _4849___mcc_h249;
        bool _4853_isArray = _4848___mcc_h248;
        DAST._IExpression _4854_on = _4847___mcc_h247;
        {
          RAST._IExpr _4855_onExpr;
          DCOMP._IOwnership _4856_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4857_recIdents;
          RAST._IExpr _out1936;
          DCOMP._IOwnership _out1937;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1938;
          (this).GenExpr(_4854_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1936, out _out1937, out _out1938);
          _4855_onExpr = _out1936;
          _4856_onOwned = _out1937;
          _4857_recIdents = _out1938;
          readIdents = _4857_recIdents;
          Dafny.ISequence<Dafny.Rune> _4858_methodName;
          _4858_methodName = (((_4852_low).is_Some) ? ((((_4851_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_4851_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
          Dafny.ISequence<RAST._IExpr> _4859_arguments;
          _4859_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          Std.Wrappers._IOption<DAST._IExpression> _source178 = _4852_low;
          if (_source178.is_None) {
          } else {
            DAST._IExpression _4860___mcc_h280 = _source178.dtor_value;
            DAST._IExpression _4861_l = _4860___mcc_h280;
            {
              RAST._IExpr _4862_lExpr;
              DCOMP._IOwnership _4863___v141;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4864_recIdentsL;
              RAST._IExpr _out1939;
              DCOMP._IOwnership _out1940;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1941;
              (this).GenExpr(_4861_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1939, out _out1940, out _out1941);
              _4862_lExpr = _out1939;
              _4863___v141 = _out1940;
              _4864_recIdentsL = _out1941;
              _4859_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_4859_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_4862_lExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4864_recIdentsL);
            }
          }
          Std.Wrappers._IOption<DAST._IExpression> _source179 = _4851_high;
          if (_source179.is_None) {
          } else {
            DAST._IExpression _4865___mcc_h281 = _source179.dtor_value;
            DAST._IExpression _4866_h = _4865___mcc_h281;
            {
              RAST._IExpr _4867_hExpr;
              DCOMP._IOwnership _4868___v142;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4869_recIdentsH;
              RAST._IExpr _out1942;
              DCOMP._IOwnership _out1943;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1944;
              (this).GenExpr(_4866_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1942, out _out1943, out _out1944);
              _4867_hExpr = _out1942;
              _4868___v142 = _out1943;
              _4869_recIdentsH = _out1944;
              _4859_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_4859_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_4867_hExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4869_recIdentsH);
            }
          }
          r = _4855_onExpr;
          if (_4853_isArray) {
            if (!(_4858_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
              _4858_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _4858_methodName);
            }
            r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _4858_methodName))).Apply(_4859_arguments);
          } else {
            if (!(_4858_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
              r = ((r).Sel(_4858_methodName)).Apply(_4859_arguments);
            }
          }
          RAST._IExpr _out1945;
          DCOMP._IOwnership _out1946;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1945, out _out1946);
          r = _out1945;
          resultingOwnership = _out1946;
          return ;
        }
      } else if (_source174.is_TupleSelect) {
        DAST._IExpression _4870___mcc_h251 = _source174.dtor_expr;
        BigInteger _4871___mcc_h252 = _source174.dtor_index;
        DAST._IType _4872___mcc_h253 = _source174.dtor_fieldType;
        DAST._IType _4873_fieldType = _4872___mcc_h253;
        BigInteger _4874_idx = _4871___mcc_h252;
        DAST._IExpression _4875_on = _4870___mcc_h251;
        {
          RAST._IExpr _4876_onExpr;
          DCOMP._IOwnership _4877_onOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4878_recIdents;
          RAST._IExpr _out1947;
          DCOMP._IOwnership _out1948;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1949;
          (this).GenExpr(_4875_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1947, out _out1948, out _out1949);
          _4876_onExpr = _out1947;
          _4877_onOwnership = _out1948;
          _4878_recIdents = _out1949;
          r = (_4876_onExpr).Sel(Std.Strings.__default.OfNat(_4874_idx));
          RAST._IExpr _out1950;
          DCOMP._IOwnership _out1951;
          DCOMP.COMP.FromOwnership(r, _4877_onOwnership, expectedOwnership, out _out1950, out _out1951);
          r = _out1950;
          resultingOwnership = _out1951;
          readIdents = _4878_recIdents;
          return ;
        }
      } else if (_source174.is_Call) {
        DAST._IExpression _4879___mcc_h254 = _source174.dtor_on;
        DAST._ICallName _4880___mcc_h255 = _source174.dtor_callName;
        Dafny.ISequence<DAST._IType> _4881___mcc_h256 = _source174.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _4882___mcc_h257 = _source174.dtor_args;
        Dafny.ISequence<DAST._IExpression> _4883_args = _4882___mcc_h257;
        Dafny.ISequence<DAST._IType> _4884_typeArgs = _4881___mcc_h256;
        DAST._ICallName _4885_name = _4880___mcc_h255;
        DAST._IExpression _4886_on = _4879___mcc_h254;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          RAST._IExpr _4887_onExpr;
          DCOMP._IOwnership _4888___v143;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4889_recIdents;
          RAST._IExpr _out1952;
          DCOMP._IOwnership _out1953;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1954;
          (this).GenExpr(_4886_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1952, out _out1953, out _out1954);
          _4887_onExpr = _out1952;
          _4888___v143 = _out1953;
          _4889_recIdents = _out1954;
          Dafny.ISequence<RAST._IType> _4890_typeExprs;
          _4890_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
          if ((new BigInteger((_4884_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _hi35 = new BigInteger((_4884_typeArgs).Count);
            for (BigInteger _4891_typeI = BigInteger.Zero; _4891_typeI < _hi35; _4891_typeI++) {
              RAST._IType _4892_typeExpr;
              RAST._IType _out1955;
              _out1955 = (this).GenType((_4884_typeArgs).Select(_4891_typeI), false, false);
              _4892_typeExpr = _out1955;
              _4890_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_4890_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_4892_typeExpr));
            }
          }
          Dafny.ISequence<RAST._IExpr> _4893_argExprs;
          _4893_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi36 = new BigInteger((_4883_args).Count);
          for (BigInteger _4894_i = BigInteger.Zero; _4894_i < _hi36; _4894_i++) {
            DCOMP._IOwnership _4895_argOwnership;
            _4895_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            if (((_4885_name).is_CallName) && ((_4894_i) < (new BigInteger((((_4885_name).dtor_signature)).Count)))) {
              RAST._IType _4896_tpe;
              RAST._IType _out1956;
              _out1956 = (this).GenType(((((_4885_name).dtor_signature)).Select(_4894_i)).dtor_typ, false, false);
              _4896_tpe = _out1956;
              if ((_4896_tpe).CanReadWithoutClone()) {
                _4895_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
              }
            }
            RAST._IExpr _4897_argExpr;
            DCOMP._IOwnership _4898___v144;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4899_argIdents;
            RAST._IExpr _out1957;
            DCOMP._IOwnership _out1958;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1959;
            (this).GenExpr((_4883_args).Select(_4894_i), selfIdent, env, _4895_argOwnership, out _out1957, out _out1958, out _out1959);
            _4897_argExpr = _out1957;
            _4898___v144 = _out1958;
            _4899_argIdents = _out1959;
            _4893_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_4893_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_4897_argExpr));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4899_argIdents);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4889_recIdents);
          Dafny.ISequence<Dafny.Rune> _4900_renderedName;
          _4900_renderedName = ((System.Func<DAST._ICallName, Dafny.ISequence<Dafny.Rune>>)((_source180) => {
            if (_source180.is_CallName) {
              Dafny.ISequence<Dafny.Rune> _4901___mcc_h282 = _source180.dtor_name;
              Std.Wrappers._IOption<DAST._IType> _4902___mcc_h283 = _source180.dtor_onType;
              Dafny.ISequence<DAST._IFormal> _4903___mcc_h284 = _source180.dtor_signature;
              Dafny.ISequence<Dafny.Rune> _4904_ident = _4901___mcc_h282;
              return DCOMP.__default.escapeName(_4904_ident);
            } else if (_source180.is_MapBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else if (_source180.is_MapBuilderBuild) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            } else if (_source180.is_SetBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            }
          }))(_4885_name);
          DAST._IExpression _source181 = _4886_on;
          if (_source181.is_Literal) {
            DAST._ILiteral _4905___mcc_h285 = _source181.dtor_Literal_i_a0;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _4906___mcc_h287 = _source181.dtor_Ident_i_a0;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4907___mcc_h289 = _source181.dtor_Companion_i_a0;
            {
              _4887_onExpr = (_4887_onExpr).MSel(_4900_renderedName);
            }
          } else if (_source181.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _4908___mcc_h291 = _source181.dtor_Tuple_i_a0;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4909___mcc_h293 = _source181.dtor_path;
            Dafny.ISequence<DAST._IType> _4910___mcc_h294 = _source181.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _4911___mcc_h295 = _source181.dtor_args;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _4912___mcc_h299 = _source181.dtor_dims;
            DAST._IType _4913___mcc_h300 = _source181.dtor_typ;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_DatatypeValue) {
            DAST._IDatatypeType _4914___mcc_h303 = _source181.dtor_datatypeType;
            Dafny.ISequence<DAST._IType> _4915___mcc_h304 = _source181.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _4916___mcc_h305 = _source181.dtor_variant;
            bool _4917___mcc_h306 = _source181.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _4918___mcc_h307 = _source181.dtor_contents;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_Convert) {
            DAST._IExpression _4919___mcc_h313 = _source181.dtor_value;
            DAST._IType _4920___mcc_h314 = _source181.dtor_from;
            DAST._IType _4921___mcc_h315 = _source181.dtor_typ;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_SeqConstruct) {
            DAST._IExpression _4922___mcc_h319 = _source181.dtor_length;
            DAST._IExpression _4923___mcc_h320 = _source181.dtor_elem;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _4924___mcc_h323 = _source181.dtor_elements;
            DAST._IType _4925___mcc_h324 = _source181.dtor_typ;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _4926___mcc_h327 = _source181.dtor_elements;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_MultisetValue) {
            Dafny.ISequence<DAST._IExpression> _4927___mcc_h329 = _source181.dtor_elements;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_MapValue) {
            Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _4928___mcc_h331 = _source181.dtor_mapElems;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_MapBuilder) {
            DAST._IType _4929___mcc_h333 = _source181.dtor_keyType;
            DAST._IType _4930___mcc_h334 = _source181.dtor_valueType;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_SeqUpdate) {
            DAST._IExpression _4931___mcc_h337 = _source181.dtor_expr;
            DAST._IExpression _4932___mcc_h338 = _source181.dtor_indexExpr;
            DAST._IExpression _4933___mcc_h339 = _source181.dtor_value;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_MapUpdate) {
            DAST._IExpression _4934___mcc_h343 = _source181.dtor_expr;
            DAST._IExpression _4935___mcc_h344 = _source181.dtor_indexExpr;
            DAST._IExpression _4936___mcc_h345 = _source181.dtor_value;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_SetBuilder) {
            DAST._IType _4937___mcc_h349 = _source181.dtor_elemType;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_ToMultiset) {
            DAST._IExpression _4938___mcc_h351 = _source181.dtor_ToMultiset_i_a0;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_This) {
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_Ite) {
            DAST._IExpression _4939___mcc_h353 = _source181.dtor_cond;
            DAST._IExpression _4940___mcc_h354 = _source181.dtor_thn;
            DAST._IExpression _4941___mcc_h355 = _source181.dtor_els;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_UnOp) {
            DAST._IUnaryOp _4942___mcc_h359 = _source181.dtor_unOp;
            DAST._IExpression _4943___mcc_h360 = _source181.dtor_expr;
            DAST.Format._IUnaryOpFormat _4944___mcc_h361 = _source181.dtor_format1;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_BinOp) {
            DAST._IBinOp _4945___mcc_h365 = _source181.dtor_op;
            DAST._IExpression _4946___mcc_h366 = _source181.dtor_left;
            DAST._IExpression _4947___mcc_h367 = _source181.dtor_right;
            DAST.Format._IBinaryOpFormat _4948___mcc_h368 = _source181.dtor_format2;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_ArrayLen) {
            DAST._IExpression _4949___mcc_h373 = _source181.dtor_expr;
            BigInteger _4950___mcc_h374 = _source181.dtor_dim;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_MapKeys) {
            DAST._IExpression _4951___mcc_h377 = _source181.dtor_expr;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_MapValues) {
            DAST._IExpression _4952___mcc_h379 = _source181.dtor_expr;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_Select) {
            DAST._IExpression _4953___mcc_h381 = _source181.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _4954___mcc_h382 = _source181.dtor_field;
            bool _4955___mcc_h383 = _source181.dtor_isConstant;
            bool _4956___mcc_h384 = _source181.dtor_onDatatype;
            DAST._IType _4957___mcc_h385 = _source181.dtor_fieldType;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_SelectFn) {
            DAST._IExpression _4958___mcc_h391 = _source181.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _4959___mcc_h392 = _source181.dtor_field;
            bool _4960___mcc_h393 = _source181.dtor_onDatatype;
            bool _4961___mcc_h394 = _source181.dtor_isStatic;
            BigInteger _4962___mcc_h395 = _source181.dtor_arity;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_Index) {
            DAST._IExpression _4963___mcc_h401 = _source181.dtor_expr;
            DAST._ICollKind _4964___mcc_h402 = _source181.dtor_collKind;
            Dafny.ISequence<DAST._IExpression> _4965___mcc_h403 = _source181.dtor_indices;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_IndexRange) {
            DAST._IExpression _4966___mcc_h407 = _source181.dtor_expr;
            bool _4967___mcc_h408 = _source181.dtor_isArray;
            Std.Wrappers._IOption<DAST._IExpression> _4968___mcc_h409 = _source181.dtor_low;
            Std.Wrappers._IOption<DAST._IExpression> _4969___mcc_h410 = _source181.dtor_high;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_TupleSelect) {
            DAST._IExpression _4970___mcc_h415 = _source181.dtor_expr;
            BigInteger _4971___mcc_h416 = _source181.dtor_index;
            DAST._IType _4972___mcc_h417 = _source181.dtor_fieldType;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_Call) {
            DAST._IExpression _4973___mcc_h421 = _source181.dtor_on;
            DAST._ICallName _4974___mcc_h422 = _source181.dtor_callName;
            Dafny.ISequence<DAST._IType> _4975___mcc_h423 = _source181.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _4976___mcc_h424 = _source181.dtor_args;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _4977___mcc_h429 = _source181.dtor_params;
            DAST._IType _4978___mcc_h430 = _source181.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _4979___mcc_h431 = _source181.dtor_body;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _4980___mcc_h435 = _source181.dtor_values;
            DAST._IType _4981___mcc_h436 = _source181.dtor_retType;
            DAST._IExpression _4982___mcc_h437 = _source181.dtor_expr;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _4983___mcc_h441 = _source181.dtor_name;
            DAST._IType _4984___mcc_h442 = _source181.dtor_typ;
            DAST._IExpression _4985___mcc_h443 = _source181.dtor_value;
            DAST._IExpression _4986___mcc_h444 = _source181.dtor_iifeBody;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_Apply) {
            DAST._IExpression _4987___mcc_h449 = _source181.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _4988___mcc_h450 = _source181.dtor_args;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_TypeTest) {
            DAST._IExpression _4989___mcc_h453 = _source181.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4990___mcc_h454 = _source181.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _4991___mcc_h455 = _source181.dtor_variant;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_InitializationValue) {
            DAST._IType _4992___mcc_h459 = _source181.dtor_typ;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_BoolBoundedPool) {
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_SetBoundedPool) {
            DAST._IExpression _4993___mcc_h461 = _source181.dtor_of;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else if (_source181.is_SeqBoundedPool) {
            DAST._IExpression _4994___mcc_h463 = _source181.dtor_of;
            bool _4995___mcc_h464 = _source181.dtor_includeDuplicates;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          } else {
            DAST._IExpression _4996___mcc_h467 = _source181.dtor_lo;
            DAST._IExpression _4997___mcc_h468 = _source181.dtor_hi;
            {
              _4887_onExpr = (_4887_onExpr).Sel(_4900_renderedName);
            }
          }
          r = _4887_onExpr;
          if ((new BigInteger((_4890_typeExprs).Count)).Sign == 1) {
            r = (r).ApplyType(_4890_typeExprs);
          }
          r = (r).Apply(_4893_argExprs);
          RAST._IExpr _out1960;
          DCOMP._IOwnership _out1961;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1960, out _out1961);
          r = _out1960;
          resultingOwnership = _out1961;
          return ;
        }
      } else if (_source174.is_Lambda) {
        Dafny.ISequence<DAST._IFormal> _4998___mcc_h258 = _source174.dtor_params;
        DAST._IType _4999___mcc_h259 = _source174.dtor_retType;
        Dafny.ISequence<DAST._IStatement> _5000___mcc_h260 = _source174.dtor_body;
        Dafny.ISequence<DAST._IStatement> _5001_body = _5000___mcc_h260;
        DAST._IType _5002_retType = _4999___mcc_h259;
        Dafny.ISequence<DAST._IFormal> _5003_paramsDafny = _4998___mcc_h258;
        {
          Dafny.ISequence<RAST._IFormal> _5004_params;
          Dafny.ISequence<RAST._IFormal> _out1962;
          _out1962 = (this).GenParams(_5003_paramsDafny);
          _5004_params = _out1962;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _5005_paramNames;
          _5005_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _5006_paramTypesMap;
          _5006_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
          BigInteger _hi37 = new BigInteger((_5004_params).Count);
          for (BigInteger _5007_i = BigInteger.Zero; _5007_i < _hi37; _5007_i++) {
            Dafny.ISequence<Dafny.Rune> _5008_name;
            _5008_name = ((_5004_params).Select(_5007_i)).dtor_name;
            _5005_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_5005_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_5008_name));
            _5006_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_5006_paramTypesMap, _5008_name, ((_5004_params).Select(_5007_i)).dtor_tpe);
          }
          DCOMP._IEnvironment _5009_env;
          _5009_env = DCOMP.Environment.create(_5005_paramNames, _5006_paramTypesMap);
          RAST._IExpr _5010_recursiveGen;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5011_recIdents;
          DCOMP._IEnvironment _5012___v149;
          RAST._IExpr _out1963;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1964;
          DCOMP._IEnvironment _out1965;
          (this).GenStmts(_5001_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), _5009_env, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out1963, out _out1964, out _out1965);
          _5010_recursiveGen = _out1963;
          _5011_recIdents = _out1964;
          _5012___v149 = _out1965;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          _5011_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_5011_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_5013_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
            var _coll6 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
            foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in (_5013_paramNames).CloneAsArray()) {
              Dafny.ISequence<Dafny.Rune> _5014_name = (Dafny.ISequence<Dafny.Rune>)_compr_6;
              if ((_5013_paramNames).Contains(_5014_name)) {
                _coll6.Add(_5014_name);
              }
            }
            return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll6);
          }))())(_5005_paramNames));
          RAST._IExpr _5015_allReadCloned;
          _5015_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          while (!(_5011_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
            Dafny.ISequence<Dafny.Rune> _5016_next;
            foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_5011_recIdents).Elements) {
              _5016_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
              if ((_5011_recIdents).Contains(_5016_next)) {
                goto after__ASSIGN_SUCH_THAT_3;
              }
            }
            throw new System.Exception("assign-such-that search produced no value (line 3681)");
          after__ASSIGN_SUCH_THAT_3: ;
            if ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) && ((_5016_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
              if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
                _5015_allReadCloned = (_5015_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
              }
            } else if (!((_5005_paramNames).Contains(_5016_next))) {
              _5015_allReadCloned = (_5015_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _5016_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.Expr.create_Identifier(_5016_next)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_5016_next));
            }
            _5011_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_5011_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_5016_next));
          }
          RAST._IType _5017_retTypeGen;
          RAST._IType _out1966;
          _out1966 = (this).GenType(_5002_retType, false, true);
          _5017_retTypeGen = _out1966;
          r = RAST.Expr.create_Block((_5015_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_5004_params, Std.Wrappers.Option<RAST._IType>.create_Some(_5017_retTypeGen), RAST.Expr.create_Block(_5010_recursiveGen)))));
          RAST._IExpr _out1967;
          DCOMP._IOwnership _out1968;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1967, out _out1968);
          r = _out1967;
          resultingOwnership = _out1968;
          return ;
        }
      } else if (_source174.is_BetaRedex) {
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _5018___mcc_h261 = _source174.dtor_values;
        DAST._IType _5019___mcc_h262 = _source174.dtor_retType;
        DAST._IExpression _5020___mcc_h263 = _source174.dtor_expr;
        DAST._IExpression _5021_expr = _5020___mcc_h263;
        DAST._IType _5022_retType = _5019___mcc_h262;
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _5023_values = _5018___mcc_h261;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _5024_paramNames;
          _5024_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<RAST._IFormal> _5025_paramFormals;
          Dafny.ISequence<RAST._IFormal> _out1969;
          _out1969 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_5026_value) => {
            return (_5026_value).dtor__0;
          })), _5023_values));
          _5025_paramFormals = _out1969;
          Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _5027_paramTypes;
          _5027_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5028_paramNamesSet;
          _5028_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _hi38 = new BigInteger((_5023_values).Count);
          for (BigInteger _5029_i = BigInteger.Zero; _5029_i < _hi38; _5029_i++) {
            Dafny.ISequence<Dafny.Rune> _5030_name;
            _5030_name = (((_5023_values).Select(_5029_i)).dtor__0).dtor_name;
            Dafny.ISequence<Dafny.Rune> _5031_rName;
            _5031_rName = DCOMP.__default.escapeName(_5030_name);
            _5024_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_5024_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_5031_rName));
            _5027_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_5027_paramTypes, _5031_rName, ((_5025_paramFormals).Select(_5029_i)).dtor_tpe);
            _5028_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_5028_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_5031_rName));
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          BigInteger _hi39 = new BigInteger((_5023_values).Count);
          for (BigInteger _5032_i = BigInteger.Zero; _5032_i < _hi39; _5032_i++) {
            RAST._IType _5033_typeGen;
            RAST._IType _out1970;
            _out1970 = (this).GenType((((_5023_values).Select(_5032_i)).dtor__0).dtor_typ, false, true);
            _5033_typeGen = _out1970;
            RAST._IExpr _5034_valueGen;
            DCOMP._IOwnership _5035___v150;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5036_recIdents;
            RAST._IExpr _out1971;
            DCOMP._IOwnership _out1972;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1973;
            (this).GenExpr(((_5023_values).Select(_5032_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1971, out _out1972, out _out1973);
            _5034_valueGen = _out1971;
            _5035___v150 = _out1972;
            _5036_recIdents = _out1973;
            r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_5023_values).Select(_5032_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_5033_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_5034_valueGen)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _5036_recIdents);
          }
          DCOMP._IEnvironment _5037_newEnv;
          _5037_newEnv = DCOMP.Environment.create(_5024_paramNames, _5027_paramTypes);
          RAST._IExpr _5038_recGen;
          DCOMP._IOwnership _5039_recOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5040_recIdents;
          RAST._IExpr _out1974;
          DCOMP._IOwnership _out1975;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1976;
          (this).GenExpr(_5021_expr, selfIdent, _5037_newEnv, expectedOwnership, out _out1974, out _out1975, out _out1976);
          _5038_recGen = _out1974;
          _5039_recOwned = _out1975;
          _5040_recIdents = _out1976;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_5040_recIdents, _5028_paramNamesSet);
          r = RAST.Expr.create_Block((r).Then(_5038_recGen));
          RAST._IExpr _out1977;
          DCOMP._IOwnership _out1978;
          DCOMP.COMP.FromOwnership(r, _5039_recOwned, expectedOwnership, out _out1977, out _out1978);
          r = _out1977;
          resultingOwnership = _out1978;
          return ;
        }
      } else if (_source174.is_IIFE) {
        Dafny.ISequence<Dafny.Rune> _5041___mcc_h264 = _source174.dtor_name;
        DAST._IType _5042___mcc_h265 = _source174.dtor_typ;
        DAST._IExpression _5043___mcc_h266 = _source174.dtor_value;
        DAST._IExpression _5044___mcc_h267 = _source174.dtor_iifeBody;
        DAST._IExpression _5045_iifeBody = _5044___mcc_h267;
        DAST._IExpression _5046_value = _5043___mcc_h266;
        DAST._IType _5047_tpe = _5042___mcc_h265;
        Dafny.ISequence<Dafny.Rune> _5048_name = _5041___mcc_h264;
        {
          RAST._IExpr _5049_valueGen;
          DCOMP._IOwnership _5050___v151;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5051_recIdents;
          RAST._IExpr _out1979;
          DCOMP._IOwnership _out1980;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1981;
          (this).GenExpr(_5046_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1979, out _out1980, out _out1981);
          _5049_valueGen = _out1979;
          _5050___v151 = _out1980;
          _5051_recIdents = _out1981;
          readIdents = _5051_recIdents;
          RAST._IType _5052_valueTypeGen;
          RAST._IType _out1982;
          _out1982 = (this).GenType(_5047_tpe, false, true);
          _5052_valueTypeGen = _out1982;
          RAST._IExpr _5053_bodyGen;
          DCOMP._IOwnership _5054___v152;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5055_bodyIdents;
          RAST._IExpr _out1983;
          DCOMP._IOwnership _out1984;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1985;
          (this).GenExpr(_5045_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1983, out _out1984, out _out1985);
          _5053_bodyGen = _out1983;
          _5054___v152 = _out1984;
          _5055_bodyIdents = _out1985;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_5055_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_5048_name)))));
          r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_5048_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_5052_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_5049_valueGen))).Then(_5053_bodyGen));
          RAST._IExpr _out1986;
          DCOMP._IOwnership _out1987;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1986, out _out1987);
          r = _out1986;
          resultingOwnership = _out1987;
          return ;
        }
      } else if (_source174.is_Apply) {
        DAST._IExpression _5056___mcc_h268 = _source174.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _5057___mcc_h269 = _source174.dtor_args;
        Dafny.ISequence<DAST._IExpression> _5058_args = _5057___mcc_h269;
        DAST._IExpression _5059_func = _5056___mcc_h268;
        {
          RAST._IExpr _5060_funcExpr;
          DCOMP._IOwnership _5061___v153;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5062_recIdents;
          RAST._IExpr _out1988;
          DCOMP._IOwnership _out1989;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1990;
          (this).GenExpr(_5059_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1988, out _out1989, out _out1990);
          _5060_funcExpr = _out1988;
          _5061___v153 = _out1989;
          _5062_recIdents = _out1990;
          readIdents = _5062_recIdents;
          Dafny.ISequence<RAST._IExpr> _5063_rArgs;
          _5063_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi40 = new BigInteger((_5058_args).Count);
          for (BigInteger _5064_i = BigInteger.Zero; _5064_i < _hi40; _5064_i++) {
            RAST._IExpr _5065_argExpr;
            DCOMP._IOwnership _5066_argOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5067_argIdents;
            RAST._IExpr _out1991;
            DCOMP._IOwnership _out1992;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1993;
            (this).GenExpr((_5058_args).Select(_5064_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1991, out _out1992, out _out1993);
            _5065_argExpr = _out1991;
            _5066_argOwned = _out1992;
            _5067_argIdents = _out1993;
            _5063_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_5063_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_5065_argExpr));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _5067_argIdents);
          }
          r = (_5060_funcExpr).Apply(_5063_rArgs);
          RAST._IExpr _out1994;
          DCOMP._IOwnership _out1995;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1994, out _out1995);
          r = _out1994;
          resultingOwnership = _out1995;
          return ;
        }
      } else if (_source174.is_TypeTest) {
        DAST._IExpression _5068___mcc_h270 = _source174.dtor_on;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _5069___mcc_h271 = _source174.dtor_dType;
        Dafny.ISequence<Dafny.Rune> _5070___mcc_h272 = _source174.dtor_variant;
        Dafny.ISequence<Dafny.Rune> _5071_variant = _5070___mcc_h272;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _5072_dType = _5069___mcc_h271;
        DAST._IExpression _5073_on = _5068___mcc_h270;
        {
          RAST._IExpr _5074_exprGen;
          DCOMP._IOwnership _5075___v154;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5076_recIdents;
          RAST._IExpr _out1996;
          DCOMP._IOwnership _out1997;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1998;
          (this).GenExpr(_5073_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1996, out _out1997, out _out1998);
          _5074_exprGen = _out1996;
          _5075___v154 = _out1997;
          _5076_recIdents = _out1998;
          RAST._IType _5077_dTypePath;
          RAST._IType _out1999;
          _out1999 = DCOMP.COMP.GenPath(_5072_dType);
          _5077_dTypePath = _out1999;
          r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_5074_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_5077_dTypePath).MSel(DCOMP.__default.escapeName(_5071_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
          RAST._IExpr _out2000;
          DCOMP._IOwnership _out2001;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2000, out _out2001);
          r = _out2000;
          resultingOwnership = _out2001;
          readIdents = _5076_recIdents;
          return ;
        }
      } else if (_source174.is_InitializationValue) {
        DAST._IType _5078___mcc_h273 = _source174.dtor_typ;
        DAST._IType _5079_typ = _5078___mcc_h273;
        {
          RAST._IType _5080_typExpr;
          RAST._IType _out2002;
          _out2002 = (this).GenType(_5079_typ, false, false);
          _5080_typExpr = _out2002;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_5080_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
          RAST._IExpr _out2003;
          DCOMP._IOwnership _out2004;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2003, out _out2004);
          r = _out2003;
          resultingOwnership = _out2004;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source174.is_BoolBoundedPool) {
        {
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
          RAST._IExpr _out2005;
          DCOMP._IOwnership _out2006;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2005, out _out2006);
          r = _out2005;
          resultingOwnership = _out2006;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source174.is_SetBoundedPool) {
        DAST._IExpression _5081___mcc_h274 = _source174.dtor_of;
        DAST._IExpression _5082_of = _5081___mcc_h274;
        {
          RAST._IExpr _5083_exprGen;
          DCOMP._IOwnership _5084___v155;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5085_recIdents;
          RAST._IExpr _out2007;
          DCOMP._IOwnership _out2008;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2009;
          (this).GenExpr(_5082_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out2007, out _out2008, out _out2009);
          _5083_exprGen = _out2007;
          _5084___v155 = _out2008;
          _5085_recIdents = _out2009;
          r = ((((_5083_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out2010;
          DCOMP._IOwnership _out2011;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2010, out _out2011);
          r = _out2010;
          resultingOwnership = _out2011;
          readIdents = _5085_recIdents;
          return ;
        }
      } else if (_source174.is_SeqBoundedPool) {
        DAST._IExpression _5086___mcc_h275 = _source174.dtor_of;
        bool _5087___mcc_h276 = _source174.dtor_includeDuplicates;
        bool _5088_includeDuplicates = _5087___mcc_h276;
        DAST._IExpression _5089_of = _5086___mcc_h275;
        {
          RAST._IExpr _5090_exprGen;
          DCOMP._IOwnership _5091___v156;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5092_recIdents;
          RAST._IExpr _out2012;
          DCOMP._IOwnership _out2013;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2014;
          (this).GenExpr(_5089_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out2012, out _out2013, out _out2014);
          _5090_exprGen = _out2012;
          _5091___v156 = _out2013;
          _5092_recIdents = _out2014;
          r = ((_5090_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          if (!(_5088_includeDuplicates)) {
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
          }
          RAST._IExpr _out2015;
          DCOMP._IOwnership _out2016;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2015, out _out2016);
          r = _out2015;
          resultingOwnership = _out2016;
          readIdents = _5092_recIdents;
          return ;
        }
      } else {
        DAST._IExpression _5093___mcc_h277 = _source174.dtor_lo;
        DAST._IExpression _5094___mcc_h278 = _source174.dtor_hi;
        DAST._IExpression _5095_hi = _5094___mcc_h278;
        DAST._IExpression _5096_lo = _5093___mcc_h277;
        {
          RAST._IExpr _5097_lo;
          DCOMP._IOwnership _5098___v157;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5099_recIdentsLo;
          RAST._IExpr _out2017;
          DCOMP._IOwnership _out2018;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2019;
          (this).GenExpr(_5096_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out2017, out _out2018, out _out2019);
          _5097_lo = _out2017;
          _5098___v157 = _out2018;
          _5099_recIdentsLo = _out2019;
          RAST._IExpr _5100_hi;
          DCOMP._IOwnership _5101___v158;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5102_recIdentsHi;
          RAST._IExpr _out2020;
          DCOMP._IOwnership _out2021;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2022;
          (this).GenExpr(_5095_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out2020, out _out2021, out _out2022);
          _5100_hi = _out2020;
          _5101___v158 = _out2021;
          _5102_recIdentsHi = _out2022;
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_5097_lo, _5100_hi));
          RAST._IExpr _out2023;
          DCOMP._IOwnership _out2024;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2023, out _out2024);
          r = _out2023;
          resultingOwnership = _out2024;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_5099_recIdentsLo, _5102_recIdentsHi);
          return ;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      BigInteger _5103_i;
      _5103_i = BigInteger.Zero;
      while ((_5103_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _5104_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _5105_m;
        RAST._IMod _out2025;
        _out2025 = (this).GenModule((p).Select(_5103_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _5105_m = _out2025;
        _5104_generated = (_5105_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_5103_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _5104_generated);
        _5103_i = (_5103_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _5106_i;
      _5106_i = BigInteger.Zero;
      while ((_5106_i) < (new BigInteger((fullName).Count))) {
        if ((_5106_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_5106_i)));
        _5106_i = (_5106_i) + (BigInteger.One);
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("();\n}"));
      return s;
    }
    public bool _i_UnicodeChars {get; set;}
    public bool UnicodeChars { get {
      return this._i_UnicodeChars;
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