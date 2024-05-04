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
      Dafny.ISequence<Dafny.Rune> _2233___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_2233___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _2233___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_2233___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in115 = (i).Drop(new BigInteger(2));
        i = _in115;
        goto TAIL_CALL_START;
      } else {
        _2233___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_2233___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in116 = (i).Drop(BigInteger.One);
        i = _in116;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _2234___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_2234___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _2234___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_2234___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in117 = (i).Drop(BigInteger.One);
        i = _in117;
        goto TAIL_CALL_START;
      } else {
        _2234___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_2234___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _2235_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _2235_r);
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
      BigInteger _2236_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _2236_indexInEnv), ((this).dtor_names).Drop((_2236_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
      Dafny.ISequence<Dafny.Rune> _2237_modName;
      _2237_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_2237_modName);
      } else {
        Dafny.ISequence<RAST._IModDecl> _2238_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _2238_body = _out15;
        s = RAST.Mod.create_Mod(_2237_modName, _2238_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi5 = new BigInteger((body).Count);
      for (BigInteger _2239_i = BigInteger.Zero; _2239_i < _hi5; _2239_i++) {
        Dafny.ISequence<RAST._IModDecl> _2240_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source70 = (body).Select(_2239_i);
        if (_source70.is_Module) {
          DAST._IModule _2241___mcc_h0 = _source70.dtor_Module_i_a0;
          DAST._IModule _2242_m = _2241___mcc_h0;
          RAST._IMod _2243_mm;
          RAST._IMod _out16;
          _out16 = (this).GenModule(_2242_m, containingPath);
          _2243_mm = _out16;
          _2240_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_2243_mm));
        } else if (_source70.is_Class) {
          DAST._IClass _2244___mcc_h1 = _source70.dtor_Class_i_a0;
          DAST._IClass _2245_c = _2244___mcc_h1;
          Dafny.ISequence<RAST._IModDecl> _out17;
          _out17 = (this).GenClass(_2245_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_2245_c).dtor_name)));
          _2240_generated = _out17;
        } else if (_source70.is_Trait) {
          DAST._ITrait _2246___mcc_h2 = _source70.dtor_Trait_i_a0;
          DAST._ITrait _2247_t = _2246___mcc_h2;
          Dafny.ISequence<Dafny.Rune> _2248_tt;
          Dafny.ISequence<Dafny.Rune> _out18;
          _out18 = (this).GenTrait(_2247_t, containingPath);
          _2248_tt = _out18;
          _2240_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_RawDecl(_2248_tt));
        } else if (_source70.is_Newtype) {
          DAST._INewtype _2249___mcc_h3 = _source70.dtor_Newtype_i_a0;
          DAST._INewtype _2250_n = _2249___mcc_h3;
          Dafny.ISequence<RAST._IModDecl> _out19;
          _out19 = (this).GenNewtype(_2250_n);
          _2240_generated = _out19;
        } else if (_source70.is_SynonymType) {
          DAST._ISynonymType _2251___mcc_h4 = _source70.dtor_SynonymType_i_a0;
          DAST._ISynonymType _2252_s = _2251___mcc_h4;
          Dafny.ISequence<RAST._IModDecl> _out20;
          _out20 = (this).GenSynonymType(_2252_s);
          _2240_generated = _out20;
        } else {
          DAST._IDatatype _2253___mcc_h5 = _source70.dtor_Datatype_i_a0;
          DAST._IDatatype _2254_d = _2253___mcc_h5;
          Dafny.ISequence<RAST._IModDecl> _out21;
          _out21 = (this).GenDatatype(_2254_d);
          _2240_generated = _out21;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _2240_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _2255_genTpConstraint;
      _2255_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _2255_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_2255_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _2255_genTpConstraint);
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
        for (BigInteger _2256_tpI = BigInteger.Zero; _2256_tpI < _hi6; _2256_tpI++) {
          DAST._ITypeArgDecl _2257_tp;
          _2257_tp = (@params).Select(_2256_tpI);
          DAST._IType _2258_typeArg;
          RAST._ITypeParamDecl _2259_typeParam;
          DAST._IType _out22;
          RAST._ITypeParamDecl _out23;
          (this).GenTypeParam(_2257_tp, out _out22, out _out23);
          _2258_typeArg = _out22;
          _2259_typeParam = _out23;
          RAST._IType _2260_rType;
          RAST._IType _out24;
          _out24 = (this).GenType(_2258_typeArg, false, false);
          _2260_rType = _out24;
          typeParamsSet = Dafny.Set<DAST._IType>.Union(typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_2258_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_2260_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_2259_typeParam));
        }
      }
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _2261_typeParamsSet;
      Dafny.ISequence<RAST._IType> _2262_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2263_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _2264_whereConstraints;
      Dafny.ISet<DAST._IType> _out25;
      Dafny.ISequence<RAST._IType> _out26;
      Dafny.ISequence<RAST._ITypeParamDecl> _out27;
      Dafny.ISequence<Dafny.Rune> _out28;
      (this).GenTypeParameters((c).dtor_typeParams, out _out25, out _out26, out _out27, out _out28);
      _2261_typeParamsSet = _out25;
      _2262_rTypeParams = _out26;
      _2263_rTypeParamsDecls = _out27;
      _2264_whereConstraints = _out28;
      Dafny.ISequence<Dafny.Rune> _2265_constrainedTypeParams;
      _2265_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_2263_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _2266_fields;
      _2266_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _2267_fieldInits;
      _2267_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _2268_fieldI = BigInteger.Zero; _2268_fieldI < _hi7; _2268_fieldI++) {
        DAST._IField _2269_field;
        _2269_field = ((c).dtor_fields).Select(_2268_fieldI);
        RAST._IType _2270_fieldType;
        RAST._IType _out29;
        _out29 = (this).GenType(((_2269_field).dtor_formal).dtor_typ, false, false);
        _2270_fieldType = _out29;
        Dafny.ISequence<Dafny.Rune> _2271_fieldRustName;
        _2271_fieldRustName = DCOMP.__default.escapeName(((_2269_field).dtor_formal).dtor_name);
        _2266_fields = Dafny.Sequence<RAST._IField>.Concat(_2266_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_2271_fieldRustName, _2270_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source71 = (_2269_field).dtor_defaultValue;
        if (_source71.is_None) {
          {
            RAST._IExpr _2272_default;
            _2272_default = RAST.__default.std__Default__default;
            _2267_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2267_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_2271_fieldRustName, _2272_default)));
          }
        } else {
          DAST._IExpression _2273___mcc_h0 = _source71.dtor_value;
          DAST._IExpression _2274_e = _2273___mcc_h0;
          {
            RAST._IExpr _2275_expr;
            DCOMP._IOwnership _2276___v40;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2277___v41;
            RAST._IExpr _out30;
            DCOMP._IOwnership _out31;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
            (this).GenExpr(_2274_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
            _2275_expr = _out30;
            _2276___v40 = _out31;
            _2277___v41 = _out32;
            _2267_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2267_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_2269_field).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cell::RefCell::new("), (_2275_expr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))))));
          }
        }
      }
      BigInteger _hi8 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _2278_typeParamI = BigInteger.Zero; _2278_typeParamI < _hi8; _2278_typeParamI++) {
        DAST._IType _2279_typeArg;
        RAST._ITypeParamDecl _2280_typeParam;
        DAST._IType _out33;
        RAST._ITypeParamDecl _out34;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_2278_typeParamI), out _out33, out _out34);
        _2279_typeArg = _out33;
        _2280_typeParam = _out34;
        RAST._IType _2281_rTypeArg;
        RAST._IType _out35;
        _out35 = (this).GenType(_2279_typeArg, false, false);
        _2281_rTypeArg = _out35;
        _2266_fields = Dafny.Sequence<RAST._IField>.Concat(_2266_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_2278_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_2281_rTypeArg))))));
        _2267_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2267_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_2278_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      Dafny.ISequence<Dafny.Rune> _2282_datatypeName;
      _2282_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IStruct _2283_struct;
      _2283_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _2282_datatypeName, _2263_rTypeParamsDecls, RAST.Fields.create_NamedFields(_2266_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_2283_struct));
      Dafny.ISequence<RAST._IImplMember> _2284_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _2285_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out36;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out37;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(path, (c).dtor_attributes))), _2261_typeParamsSet, out _out36, out _out37);
      _2284_implBodyRaw = _out36;
      _2285_traitBodies = _out37;
      Dafny.ISequence<RAST._IImplMember> _2286_implBody;
      _2286_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(RAST.Expr.create_Identifier(_2282_datatypeName), _2267_fieldInits))))), _2284_implBodyRaw);
      RAST._IImpl _2287_i;
      _2287_i = RAST.Impl.create_Impl(_2263_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2282_datatypeName), _2262_rTypeParams), _2264_whereConstraints, _2286_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_2287_i)));
      if ((new BigInteger(((c).dtor_superClasses).Count)).Sign == 1) {
        BigInteger _2288_i;
        _2288_i = BigInteger.Zero;
        while ((_2288_i) < (new BigInteger(((c).dtor_superClasses).Count))) {
          DAST._IType _2289_superClass;
          _2289_superClass = ((c).dtor_superClasses).Select(_2288_i);
          DAST._IType _source72 = _2289_superClass;
          if (_source72.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2290___mcc_h1 = _source72.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _2291___mcc_h2 = _source72.dtor_typeArgs;
            DAST._IResolvedType _2292___mcc_h3 = _source72.dtor_resolved;
            DAST._IResolvedType _source73 = _2292___mcc_h3;
            if (_source73.is_Datatype) {
              DAST._IDatatypeType _2293___mcc_h7 = _source73.dtor_datatypeType;
            } else if (_source73.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2294___mcc_h9 = _source73.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _2295___mcc_h10 = _source73.dtor_attributes;
              Dafny.ISequence<DAST._IType> _2296_typeArgs = _2291___mcc_h2;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2297_traitPath = _2290___mcc_h1;
              {
                RAST._IType _2298_pathStr;
                RAST._IType _out38;
                _out38 = DCOMP.COMP.GenPath(_2297_traitPath);
                _2298_pathStr = _out38;
                Dafny.ISequence<RAST._IType> _2299_typeArgs;
                Dafny.ISequence<RAST._IType> _out39;
                _out39 = (this).GenTypeArgs(_2296_typeArgs, false, false);
                _2299_typeArgs = _out39;
                Dafny.ISequence<RAST._IImplMember> _2300_body;
                _2300_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_2285_traitBodies).Contains(_2297_traitPath)) {
                  _2300_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_2285_traitBodies,_2297_traitPath);
                }
                RAST._IType _2301_genSelfPath;
                RAST._IType _out40;
                _out40 = DCOMP.COMP.GenPath(path);
                _2301_genSelfPath = _out40;
                RAST._IModDecl _2302_x;
                _2302_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2263_rTypeParamsDecls, RAST.Type.create_TypeApp(_2298_pathStr, _2299_typeArgs), RAST.__default.Rc(RAST.Type.create_TypeApp(_2301_genSelfPath, _2262_rTypeParams)), _2264_whereConstraints, _2300_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_2302_x));
              }
            } else {
              DAST._IType _2303___mcc_h13 = _source73.dtor_baseType;
              DAST._INewtypeRange _2304___mcc_h14 = _source73.dtor_range;
              bool _2305___mcc_h15 = _source73.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _2306___mcc_h16 = _source73.dtor_attributes;
            }
          } else if (_source72.is_Nullable) {
            DAST._IType _2307___mcc_h21 = _source72.dtor_Nullable_i_a0;
          } else if (_source72.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2308___mcc_h23 = _source72.dtor_Tuple_i_a0;
          } else if (_source72.is_Array) {
            DAST._IType _2309___mcc_h25 = _source72.dtor_element;
            BigInteger _2310___mcc_h26 = _source72.dtor_dims;
          } else if (_source72.is_Seq) {
            DAST._IType _2311___mcc_h29 = _source72.dtor_element;
          } else if (_source72.is_Set) {
            DAST._IType _2312___mcc_h31 = _source72.dtor_element;
          } else if (_source72.is_Multiset) {
            DAST._IType _2313___mcc_h33 = _source72.dtor_element;
          } else if (_source72.is_Map) {
            DAST._IType _2314___mcc_h35 = _source72.dtor_key;
            DAST._IType _2315___mcc_h36 = _source72.dtor_value;
          } else if (_source72.is_SetBuilder) {
            DAST._IType _2316___mcc_h39 = _source72.dtor_element;
          } else if (_source72.is_MapBuilder) {
            DAST._IType _2317___mcc_h41 = _source72.dtor_key;
            DAST._IType _2318___mcc_h42 = _source72.dtor_value;
          } else if (_source72.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2319___mcc_h45 = _source72.dtor_args;
            DAST._IType _2320___mcc_h46 = _source72.dtor_result;
          } else if (_source72.is_Primitive) {
            DAST._IPrimitive _2321___mcc_h49 = _source72.dtor_Primitive_i_a0;
          } else if (_source72.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2322___mcc_h51 = _source72.dtor_Passthrough_i_a0;
          } else {
            Dafny.ISequence<Dafny.Rune> _2323___mcc_h53 = _source72.dtor_TypeArg_i_a0;
          }
          _2288_i = (_2288_i) + (BigInteger.One);
        }
      }
      RAST._IImpl _2324_d;
      _2324_d = RAST.Impl.create_ImplFor(_2263_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2282_datatypeName), _2262_rTypeParams), _2264_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(_2282_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new()"))))))));
      Dafny.ISequence<RAST._IModDecl> _2325_defaultImpl;
      _2325_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_2324_d));
      RAST._IImpl _2326_p;
      _2326_p = RAST.Impl.create_ImplFor(_2263_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2282_datatypeName), _2262_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), DCOMP.__default.escapeName(((c).dtor_enclosingModule))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")"))))))));
      Dafny.ISequence<RAST._IModDecl> _2327_printImpl;
      _2327_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_2326_p));
      RAST._IImpl _2328_pp;
      _2328_pp = RAST.Impl.create_ImplFor(_2263_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cmp::PartialEq")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2282_datatypeName), _2262_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("eq"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.__default.SelfBorrowed)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ptr::eq(self, other)")))))));
      Dafny.ISequence<RAST._IModDecl> _2329_ptrPartialEqImpl;
      _2329_ptrPartialEqImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_2328_pp));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(s, _2325_defaultImpl), _2327_printImpl), _2329_ptrPartialEqImpl);
      return s;
    }
    public Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _2330_typeParamsSet;
      _2330_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _2331_typeParamDecls;
      _2331_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _2332_typeParams;
      _2332_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _2333_tpI;
      _2333_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        while ((_2333_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._ITypeArgDecl _2334_tp;
          _2334_tp = ((t).dtor_typeParams).Select(_2333_tpI);
          DAST._IType _2335_typeArg;
          RAST._ITypeParamDecl _2336_typeParamDecl;
          DAST._IType _out41;
          RAST._ITypeParamDecl _out42;
          (this).GenTypeParam(_2334_tp, out _out41, out _out42);
          _2335_typeArg = _out41;
          _2336_typeParamDecl = _out42;
          _2330_typeParamsSet = Dafny.Set<DAST._IType>.Union(_2330_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_2335_typeArg));
          _2331_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_2331_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_2336_typeParamDecl));
          RAST._IType _2337_typeParam;
          RAST._IType _out43;
          _out43 = (this).GenType(_2335_typeArg, false, false);
          _2337_typeParam = _out43;
          _2332_typeParams = Dafny.Sequence<RAST._IType>.Concat(_2332_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_2337_typeParam));
          _2333_tpI = (_2333_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2338_fullPath;
      _2338_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _2339_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _2340___v45;
      Dafny.ISequence<RAST._IImplMember> _out44;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out45;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_2338_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_2338_fullPath, (t).dtor_attributes)), _2330_typeParamsSet, out _out44, out _out45);
      _2339_implBody = _out44;
      _2340___v45 = _out45;
      s = (RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_2331_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _2332_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _2339_implBody)))._ToString(DCOMP.__default.IND);
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _2341_typeParamsSet;
      Dafny.ISequence<RAST._IType> _2342_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2343_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _2344_whereConstraints;
      Dafny.ISet<DAST._IType> _out46;
      Dafny.ISequence<RAST._IType> _out47;
      Dafny.ISequence<RAST._ITypeParamDecl> _out48;
      Dafny.ISequence<Dafny.Rune> _out49;
      (this).GenTypeParameters((c).dtor_typeParams, out _out46, out _out47, out _out48, out _out49);
      _2341_typeParamsSet = _out46;
      _2342_rTypeParams = _out47;
      _2343_rTypeParamsDecls = _out48;
      _2344_whereConstraints = _out49;
      Dafny.ISequence<Dafny.Rune> _2345_constrainedTypeParams;
      _2345_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_2343_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _2346_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source74 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      if (_source74.is_None) {
        RAST._IType _out50;
        _out50 = (this).GenType((c).dtor_base, false, false);
        _2346_underlyingType = _out50;
      } else {
        RAST._IType _2347___mcc_h0 = _source74.dtor_value;
        RAST._IType _2348_v = _2347___mcc_h0;
        _2346_underlyingType = _2348_v;
      }
      DAST._IType _2349_resultingType;
      _2349_resultingType = DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Newtype((c).dtor_base, (c).dtor_range, false, (c).dtor_attributes));
      Dafny.ISequence<Dafny.Rune> _2350_datatypeName;
      _2350_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _2350_datatypeName, _2343_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _2346_underlyingType))))));
      RAST._IExpr _2351_fnBody;
      _2351_fnBody = RAST.Expr.create_Identifier(_2350_datatypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source75 = (c).dtor_witnessExpr;
      if (_source75.is_None) {
        {
          _2351_fnBody = (_2351_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      } else {
        DAST._IExpression _2352___mcc_h1 = _source75.dtor_value;
        DAST._IExpression _2353_e = _2352___mcc_h1;
        {
          DAST._IExpression _2354_e;
          _2354_e = ((object.Equals((c).dtor_base, _2349_resultingType)) ? (_2353_e) : (DAST.Expression.create_Convert(_2353_e, (c).dtor_base, _2349_resultingType)));
          RAST._IExpr _2355_eStr;
          DCOMP._IOwnership _2356___v46;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2357___v47;
          RAST._IExpr _out51;
          DCOMP._IOwnership _out52;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out53;
          (this).GenExpr(_2354_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out51, out _out52, out _out53);
          _2355_eStr = _out51;
          _2356___v46 = _out52;
          _2357___v47 = _out53;
          _2351_fnBody = (_2351_fnBody).Apply1(_2355_eStr);
        }
      }
      RAST._IImplMember _2358_body;
      _2358_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2351_fnBody)));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2343_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2350_datatypeName), _2342_rTypeParams), _2344_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_2358_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2343_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2350_datatypeName), _2342_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2343_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2350_datatypeName), _2342_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_2346_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _2359_typeParamsSet;
      Dafny.ISequence<RAST._IType> _2360_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2361_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _2362_whereConstraints;
      Dafny.ISet<DAST._IType> _out54;
      Dafny.ISequence<RAST._IType> _out55;
      Dafny.ISequence<RAST._ITypeParamDecl> _out56;
      Dafny.ISequence<Dafny.Rune> _out57;
      (this).GenTypeParameters((c).dtor_typeParams, out _out54, out _out55, out _out56, out _out57);
      _2359_typeParamsSet = _out54;
      _2360_rTypeParams = _out55;
      _2361_rTypeParamsDecls = _out56;
      _2362_whereConstraints = _out57;
      Dafny.ISequence<Dafny.Rune> _2363_constrainedTypeParams;
      _2363_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_2361_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<Dafny.Rune> _2364_synonymTypeName;
      _2364_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _2365_resultingType;
      RAST._IType _out58;
      _out58 = (this).GenType((c).dtor_base, false, false);
      _2365_resultingType = _out58;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _2364_synonymTypeName, _2361_rTypeParamsDecls, _2365_resultingType)));
      Std.Wrappers._IOption<DAST._IExpression> _source76 = (c).dtor_witnessExpr;
      if (_source76.is_None) {
      } else {
        DAST._IExpression _2366___mcc_h0 = _source76.dtor_value;
        DAST._IExpression _2367_e = _2366___mcc_h0;
        {
          RAST._IExpr _2368_rStmts;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2369___v48;
          DCOMP._IEnvironment _2370_newEnv;
          RAST._IExpr _out59;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out60;
          DCOMP._IEnvironment _out61;
          (this).GenStmts((c).dtor_witnessStmts, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), false, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out59, out _out60, out _out61);
          _2368_rStmts = _out59;
          _2369___v48 = _out60;
          _2370_newEnv = _out61;
          RAST._IExpr _2371_rExpr;
          DCOMP._IOwnership _2372___v49;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2373___v50;
          RAST._IExpr _out62;
          DCOMP._IOwnership _out63;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out64;
          (this).GenExpr(_2367_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), _2370_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out62, out _out63, out _out64);
          _2371_rExpr = _out62;
          _2372___v49 = _out63;
          _2373___v50 = _out64;
          Dafny.ISequence<Dafny.Rune> _2374_constantName;
          _2374_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_2374_constantName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_2365_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_2368_rStmts).Then(_2371_rExpr)))))));
        }
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _2375_typeParamsSet;
      Dafny.ISequence<RAST._IType> _2376_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2377_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _2378_whereConstraints;
      Dafny.ISet<DAST._IType> _out65;
      Dafny.ISequence<RAST._IType> _out66;
      Dafny.ISequence<RAST._ITypeParamDecl> _out67;
      Dafny.ISequence<Dafny.Rune> _out68;
      (this).GenTypeParameters((c).dtor_typeParams, out _out65, out _out66, out _out67, out _out68);
      _2375_typeParamsSet = _out65;
      _2376_rTypeParams = _out66;
      _2377_rTypeParamsDecls = _out67;
      _2378_whereConstraints = _out68;
      Dafny.ISequence<Dafny.Rune> _2379_datatypeName;
      _2379_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _2380_ctors;
      _2380_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      BigInteger _hi9 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _2381_i = BigInteger.Zero; _2381_i < _hi9; _2381_i++) {
        DAST._IDatatypeCtor _2382_ctor;
        _2382_ctor = ((c).dtor_ctors).Select(_2381_i);
        Dafny.ISequence<RAST._IField> _2383_ctorArgs;
        _2383_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        BigInteger _hi10 = new BigInteger(((_2382_ctor).dtor_args).Count);
        for (BigInteger _2384_j = BigInteger.Zero; _2384_j < _hi10; _2384_j++) {
          DAST._IFormal _2385_formal;
          _2385_formal = ((_2382_ctor).dtor_args).Select(_2384_j);
          RAST._IType _2386_formalType;
          RAST._IType _out69;
          _out69 = (this).GenType((_2385_formal).dtor_typ, false, false);
          _2386_formalType = _out69;
          if ((c).dtor_isCo) {
            _2383_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_2383_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(DCOMP.__default.escapeName((_2385_formal).dtor_name), RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_2386_formalType))))));
          } else {
            _2383_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_2383_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(DCOMP.__default.escapeName((_2385_formal).dtor_name), _2386_formalType))));
          }
        }
        _2380_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_2380_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_2382_ctor).dtor_name), RAST.Fields.create_NamedFields(_2383_ctorArgs))));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2387_selfPath;
      _2387_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _2388_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _2389_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out70;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out71;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(_2387_selfPath, (c).dtor_attributes))), _2375_typeParamsSet, out _out70, out _out71);
      _2388_implBodyRaw = _out70;
      _2389_traitBodies = _out71;
      Dafny.ISequence<RAST._IImplMember> _2390_implBody;
      _2390_implBody = _2388_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2391_emittedFields;
      _2391_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi11 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _2392_i = BigInteger.Zero; _2392_i < _hi11; _2392_i++) {
        DAST._IDatatypeCtor _2393_ctor;
        _2393_ctor = ((c).dtor_ctors).Select(_2392_i);
        BigInteger _hi12 = new BigInteger(((_2393_ctor).dtor_args).Count);
        for (BigInteger _2394_j = BigInteger.Zero; _2394_j < _hi12; _2394_j++) {
          DAST._IFormal _2395_formal;
          _2395_formal = ((_2393_ctor).dtor_args).Select(_2394_j);
          if (!((_2391_emittedFields).Contains((_2395_formal).dtor_name))) {
            _2391_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2391_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_2395_formal).dtor_name));
            RAST._IType _2396_formalType;
            RAST._IType _out72;
            _out72 = (this).GenType((_2395_formal).dtor_typ, false, false);
            _2396_formalType = _out72;
            Dafny.ISequence<RAST._IMatchCase> _2397_cases;
            _2397_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _2398_k = BigInteger.Zero; _2398_k < _hi13; _2398_k++) {
              DAST._IDatatypeCtor _2399_ctor2;
              _2399_ctor2 = ((c).dtor_ctors).Select(_2398_k);
              Dafny.ISequence<Dafny.Rune> _2400_pattern;
              _2400_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2379_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_2399_ctor2).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
              Dafny.ISequence<Dafny.Rune> _2401_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              bool _2402_hasMatchingField;
              _2402_hasMatchingField = false;
              BigInteger _hi14 = new BigInteger(((_2399_ctor2).dtor_args).Count);
              for (BigInteger _2403_l = BigInteger.Zero; _2403_l < _hi14; _2403_l++) {
                DAST._IFormal _2404_formal2;
                _2404_formal2 = ((_2399_ctor2).dtor_args).Select(_2403_l);
                if (object.Equals((_2395_formal).dtor_name, (_2404_formal2).dtor_name)) {
                  _2402_hasMatchingField = true;
                }
                _2400_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2400_pattern, DCOMP.__default.escapeName((_2404_formal2).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2400_pattern = Dafny.Sequence<Dafny.Rune>.Concat(_2400_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              if (_2402_hasMatchingField) {
                if ((c).dtor_isCo) {
                  _2401_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), DCOMP.__default.escapeName((_2395_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _2401_rhs = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeName((_2395_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _2401_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _2405_ctorMatch;
              _2405_ctorMatch = RAST.MatchCase.create(_2400_pattern, RAST.Expr.create_RawExpr(_2401_rhs));
              _2397_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_2397_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_2405_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _2397_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_2397_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_2379_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _2406_methodBody;
            _2406_methodBody = RAST.Expr.create_Match(RAST.__default.self, _2397_cases);
            _2390_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_2390_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(DCOMP.__default.escapeName((_2395_formal).dtor_name), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_2396_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2406_methodBody)))));
          }
        }
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _2407_types;
        _2407_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi15 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _2408_typeI = BigInteger.Zero; _2408_typeI < _hi15; _2408_typeI++) {
          DAST._IType _2409_typeArg;
          RAST._ITypeParamDecl _2410_rTypeParamDecl;
          DAST._IType _out73;
          RAST._ITypeParamDecl _out74;
          (this).GenTypeParam(((c).dtor_typeParams).Select(_2408_typeI), out _out73, out _out74);
          _2409_typeArg = _out73;
          _2410_rTypeParamDecl = _out74;
          RAST._IType _2411_rTypeArg;
          RAST._IType _out75;
          _out75 = (this).GenType(_2409_typeArg, false, false);
          _2411_rTypeArg = _out75;
          _2407_types = Dafny.Sequence<RAST._IType>.Concat(_2407_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_2411_rTypeArg))));
        }
        _2380_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_2380_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_2412_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _2412_tpe);
})), _2407_types)))));
      }
      Dafny.ISequence<RAST._IModDecl> _2413_enumBody;
      _2413_enumBody = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]")), _2379_datatypeName, _2377_rTypeParamsDecls, _2380_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_2377_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2379_datatypeName), _2376_rTypeParams), _2378_whereConstraints, _2390_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _2414_printImplBodyCases;
      _2414_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _2415_i = BigInteger.Zero; _2415_i < _hi16; _2415_i++) {
        DAST._IDatatypeCtor _2416_ctor;
        _2416_ctor = ((c).dtor_ctors).Select(_2415_i);
        Dafny.ISequence<Dafny.Rune> _2417_ctorMatch;
        _2417_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeName((_2416_ctor).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
        Dafny.ISequence<Dafny.Rune> _2418_modulePrefix;
        _2418_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeName(((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        RAST._IExpr _2419_printRhs;
        _2419_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _2418_modulePrefix), DCOMP.__default.escapeName((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName((_2416_ctor).dtor_name)), (((_2416_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        BigInteger _hi17 = new BigInteger(((_2416_ctor).dtor_args).Count);
        for (BigInteger _2420_j = BigInteger.Zero; _2420_j < _hi17; _2420_j++) {
          DAST._IFormal _2421_formal;
          _2421_formal = ((_2416_ctor).dtor_args).Select(_2420_j);
          Dafny.ISequence<Dafny.Rune> _2422_formalName;
          _2422_formalName = DCOMP.__default.escapeName((_2421_formal).dtor_name);
          _2417_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2417_ctorMatch, _2422_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_2420_j).Sign == 1) {
            _2419_printRhs = (_2419_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _2419_printRhs = (_2419_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), DCOMP.__default.escapeName((_2421_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))));
        }
        _2417_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(_2417_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        if ((_2416_ctor).dtor_hasAnyArgs) {
          _2419_printRhs = (_2419_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _2419_printRhs = (_2419_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _2414_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_2414_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2379_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _2417_ctorMatch), RAST.Expr.create_Block(_2419_printRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _2414_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_2414_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_2379_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _2423_defaultConstrainedTypeParams;
      _2423_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_2377_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      RAST._IExpr _2424_printImplBody;
      _2424_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _2414_printImplBodyCases);
      Dafny.ISequence<RAST._IModDecl> _2425_printImpl;
      _2425_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2377_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2379_datatypeName), _2376_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2377_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2379_datatypeName), _2376_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2424_printImplBody)))))));
      Dafny.ISequence<RAST._IModDecl> _2426_defaultImpl;
      _2426_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _2427_structName;
        _2427_structName = (RAST.Expr.create_Identifier(_2379_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _2428_structAssignments;
        _2428_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi18 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _2429_i = BigInteger.Zero; _2429_i < _hi18; _2429_i++) {
          DAST._IFormal _2430_formal;
          _2430_formal = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_2429_i);
          _2428_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2428_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName((_2430_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _2431_defaultConstrainedTypeParams;
        _2431_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_2377_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _2432_fullType;
        _2432_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2379_datatypeName), _2376_rTypeParams);
        _2426_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2431_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _2432_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_2432_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_2427_structName, _2428_structAssignments))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(_2413_enumBody, _2425_printImpl), _2426_defaultImpl);
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
        for (BigInteger _2433_i = BigInteger.Zero; _2433_i < _hi19; _2433_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_2433_i))));
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
        for (BigInteger _2434_i = BigInteger.Zero; _2434_i < _hi20; _2434_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_2434_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding, bool inFn)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger((args).Count)).Sign == 1) {
        BigInteger _2435_i;
        _2435_i = BigInteger.Zero;
        while ((_2435_i) < (new BigInteger((args).Count))) {
          RAST._IType _2436_genTp;
          RAST._IType _out76;
          _out76 = (this).GenType((args).Select(_2435_i), inBinding, inFn);
          _2436_genTp = _out76;
          s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_2436_genTp));
          _2435_i = (_2435_i) + (BigInteger.One);
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
      DAST._IType _source77 = c;
      if (_source77.is_Path) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2437___mcc_h0 = _source77.dtor_Path_i_a0;
        Dafny.ISequence<DAST._IType> _2438___mcc_h1 = _source77.dtor_typeArgs;
        DAST._IResolvedType _2439___mcc_h2 = _source77.dtor_resolved;
        DAST._IResolvedType _2440_resolved = _2439___mcc_h2;
        Dafny.ISequence<DAST._IType> _2441_args = _2438___mcc_h1;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2442_p = _2437___mcc_h0;
        {
          RAST._IType _2443_t;
          RAST._IType _out77;
          _out77 = DCOMP.COMP.GenPath(_2442_p);
          _2443_t = _out77;
          Dafny.ISequence<RAST._IType> _2444_typeArgs;
          Dafny.ISequence<RAST._IType> _out78;
          _out78 = (this).GenTypeArgs(_2441_args, inBinding, inFn);
          _2444_typeArgs = _out78;
          s = RAST.Type.create_TypeApp(_2443_t, _2444_typeArgs);
          DAST._IResolvedType _source78 = _2440_resolved;
          if (_source78.is_Datatype) {
            DAST._IDatatypeType _2445___mcc_h21 = _source78.dtor_datatypeType;
            DAST._IDatatypeType _source79 = _2445___mcc_h21;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2446___mcc_h22 = _source79.dtor_path;
            Dafny.ISequence<DAST._IAttribute> _2447___mcc_h23 = _source79.dtor_attributes;
            Dafny.ISequence<DAST._IAttribute> _2448_attributes = _2447___mcc_h23;
          } else if (_source78.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2449___mcc_h24 = _source78.dtor_path;
            Dafny.ISequence<DAST._IAttribute> _2450___mcc_h25 = _source78.dtor_attributes;
            {
              if ((_2442_p).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
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
            DAST._IType _2451___mcc_h26 = _source78.dtor_baseType;
            DAST._INewtypeRange _2452___mcc_h27 = _source78.dtor_range;
            bool _2453___mcc_h28 = _source78.dtor_erase;
            Dafny.ISequence<DAST._IAttribute> _2454___mcc_h29 = _source78.dtor_attributes;
            Dafny.ISequence<DAST._IAttribute> _2455_attributes = _2454___mcc_h29;
            bool _2456_erased = _2453___mcc_h28;
            DAST._INewtypeRange _2457_range = _2452___mcc_h27;
            DAST._IType _2458_t = _2451___mcc_h26;
            {
              if (_2456_erased) {
                Std.Wrappers._IOption<RAST._IType> _source80 = DCOMP.COMP.NewtypeToRustType(_2458_t, _2457_range);
                if (_source80.is_None) {
                } else {
                  RAST._IType _2459___mcc_h30 = _source80.dtor_value;
                  RAST._IType _2460_v = _2459___mcc_h30;
                  s = _2460_v;
                }
              }
            }
          }
        }
      } else if (_source77.is_Nullable) {
        DAST._IType _2461___mcc_h3 = _source77.dtor_Nullable_i_a0;
        DAST._IType _2462_inner = _2461___mcc_h3;
        {
          RAST._IType _2463_innerExpr;
          RAST._IType _out79;
          _out79 = (this).GenType(_2462_inner, inBinding, inFn);
          _2463_innerExpr = _out79;
          s = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::option::Option")), Dafny.Sequence<RAST._IType>.FromElements(_2463_innerExpr));
        }
      } else if (_source77.is_Tuple) {
        Dafny.ISequence<DAST._IType> _2464___mcc_h4 = _source77.dtor_Tuple_i_a0;
        Dafny.ISequence<DAST._IType> _2465_types = _2464___mcc_h4;
        {
          Dafny.ISequence<RAST._IType> _2466_args;
          _2466_args = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _2467_i;
          _2467_i = BigInteger.Zero;
          while ((_2467_i) < (new BigInteger((_2465_types).Count))) {
            RAST._IType _2468_generated;
            RAST._IType _out80;
            _out80 = (this).GenType((_2465_types).Select(_2467_i), inBinding, inFn);
            _2468_generated = _out80;
            _2466_args = Dafny.Sequence<RAST._IType>.Concat(_2466_args, Dafny.Sequence<RAST._IType>.FromElements(_2468_generated));
            _2467_i = (_2467_i) + (BigInteger.One);
          }
          s = RAST.Type.create_TupleType(_2466_args);
        }
      } else if (_source77.is_Array) {
        DAST._IType _2469___mcc_h5 = _source77.dtor_element;
        BigInteger _2470___mcc_h6 = _source77.dtor_dims;
        BigInteger _2471_dims = _2470___mcc_h6;
        DAST._IType _2472_element = _2469___mcc_h5;
        {
          RAST._IType _2473_elem;
          RAST._IType _out81;
          _out81 = (this).GenType(_2472_element, inBinding, inFn);
          _2473_elem = _out81;
          s = _2473_elem;
          BigInteger _2474_i;
          _2474_i = BigInteger.Zero;
          while ((_2474_i) < (_2471_dims)) {
            s = RAST.__default.Rc(RAST.__default.RefCell(RAST.__default.Vec(s)));
            _2474_i = (_2474_i) + (BigInteger.One);
          }
        }
      } else if (_source77.is_Seq) {
        DAST._IType _2475___mcc_h7 = _source77.dtor_element;
        DAST._IType _2476_element = _2475___mcc_h7;
        {
          RAST._IType _2477_elem;
          RAST._IType _out82;
          _out82 = (this).GenType(_2476_element, inBinding, inFn);
          _2477_elem = _out82;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_2477_elem));
        }
      } else if (_source77.is_Set) {
        DAST._IType _2478___mcc_h8 = _source77.dtor_element;
        DAST._IType _2479_element = _2478___mcc_h8;
        {
          RAST._IType _2480_elem;
          RAST._IType _out83;
          _out83 = (this).GenType(_2479_element, inBinding, inFn);
          _2480_elem = _out83;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_2480_elem));
        }
      } else if (_source77.is_Multiset) {
        DAST._IType _2481___mcc_h9 = _source77.dtor_element;
        DAST._IType _2482_element = _2481___mcc_h9;
        {
          RAST._IType _2483_elem;
          RAST._IType _out84;
          _out84 = (this).GenType(_2482_element, inBinding, inFn);
          _2483_elem = _out84;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_2483_elem));
        }
      } else if (_source77.is_Map) {
        DAST._IType _2484___mcc_h10 = _source77.dtor_key;
        DAST._IType _2485___mcc_h11 = _source77.dtor_value;
        DAST._IType _2486_value = _2485___mcc_h11;
        DAST._IType _2487_key = _2484___mcc_h10;
        {
          RAST._IType _2488_keyType;
          RAST._IType _out85;
          _out85 = (this).GenType(_2487_key, inBinding, inFn);
          _2488_keyType = _out85;
          RAST._IType _2489_valueType;
          RAST._IType _out86;
          _out86 = (this).GenType(_2486_value, inBinding, inFn);
          _2489_valueType = _out86;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_2488_keyType, _2489_valueType));
        }
      } else if (_source77.is_SetBuilder) {
        DAST._IType _2490___mcc_h12 = _source77.dtor_element;
        DAST._IType _2491_elem = _2490___mcc_h12;
        {
          RAST._IType _2492_elemType;
          RAST._IType _out87;
          _out87 = (this).GenType(_2491_elem, inBinding, inFn);
          _2492_elemType = _out87;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_2492_elemType));
        }
      } else if (_source77.is_MapBuilder) {
        DAST._IType _2493___mcc_h13 = _source77.dtor_key;
        DAST._IType _2494___mcc_h14 = _source77.dtor_value;
        DAST._IType _2495_value = _2494___mcc_h14;
        DAST._IType _2496_key = _2493___mcc_h13;
        {
          RAST._IType _2497_keyType;
          RAST._IType _out88;
          _out88 = (this).GenType(_2496_key, inBinding, inFn);
          _2497_keyType = _out88;
          RAST._IType _2498_valueType;
          RAST._IType _out89;
          _out89 = (this).GenType(_2495_value, inBinding, inFn);
          _2498_valueType = _out89;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_2497_keyType, _2498_valueType));
        }
      } else if (_source77.is_Arrow) {
        Dafny.ISequence<DAST._IType> _2499___mcc_h15 = _source77.dtor_args;
        DAST._IType _2500___mcc_h16 = _source77.dtor_result;
        DAST._IType _2501_result = _2500___mcc_h16;
        Dafny.ISequence<DAST._IType> _2502_args = _2499___mcc_h15;
        {
          Dafny.ISequence<RAST._IType> _2503_argTypes;
          _2503_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _2504_i;
          _2504_i = BigInteger.Zero;
          while ((_2504_i) < (new BigInteger((_2502_args).Count))) {
            RAST._IType _2505_generated;
            RAST._IType _out90;
            _out90 = (this).GenType((_2502_args).Select(_2504_i), inBinding, true);
            _2505_generated = _out90;
            _2503_argTypes = Dafny.Sequence<RAST._IType>.Concat(_2503_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_2505_generated)));
            _2504_i = (_2504_i) + (BigInteger.One);
          }
          RAST._IType _2506_resultType;
          RAST._IType _out91;
          _out91 = (this).GenType(_2501_result, inBinding, (inFn) || (inBinding));
          _2506_resultType = _out91;
          s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_2503_argTypes, _2506_resultType)));
        }
      } else if (_source77.is_Primitive) {
        DAST._IPrimitive _2507___mcc_h17 = _source77.dtor_Primitive_i_a0;
        DAST._IPrimitive _2508_p = _2507___mcc_h17;
        {
          DAST._IPrimitive _source81 = _2508_p;
          if (_source81.is_Int) {
            s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
          } else if (_source81.is_Real) {
            s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
          } else if (_source81.is_String) {
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
          } else if (_source81.is_Bool) {
            s = RAST.Type.create_Bool();
          } else {
            s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
          }
        }
      } else if (_source77.is_Passthrough) {
        Dafny.ISequence<Dafny.Rune> _2509___mcc_h18 = _source77.dtor_Passthrough_i_a0;
        Dafny.ISequence<Dafny.Rune> _2510_v = _2509___mcc_h18;
        s = RAST.__default.RawType(_2510_v);
      } else {
        Dafny.ISequence<Dafny.Rune> _2511___mcc_h19 = _source77.dtor_TypeArg_i_a0;
        Dafny.ISequence<Dafny.Rune> _source82 = _2511___mcc_h19;
        Dafny.ISequence<Dafny.Rune> _2512___mcc_h20 = _source82;
        Dafny.ISequence<Dafny.Rune> _2513_name = _2512___mcc_h20;
        s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_2513_name));
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
      for (BigInteger _2514_i = BigInteger.Zero; _2514_i < _hi21; _2514_i++) {
        DAST._IMethod _source83 = (body).Select(_2514_i);
        DAST._IMethod _2515___mcc_h0 = _source83;
        DAST._IMethod _2516_m = _2515___mcc_h0;
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source84 = (_2516_m).dtor_overridingPath;
          if (_source84.is_None) {
            {
              RAST._IImplMember _2517_generated;
              RAST._IImplMember _out92;
              _out92 = (this).GenMethod(_2516_m, forTrait, enclosingType, enclosingTypeParams);
              _2517_generated = _out92;
              s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_2517_generated));
            }
          } else {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2518___mcc_h1 = _source84.dtor_value;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2519_p = _2518___mcc_h1;
            {
              Dafny.ISequence<RAST._IImplMember> _2520_existing;
              _2520_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
              if ((traitBodies).Contains(_2519_p)) {
                _2520_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_2519_p);
              }
              RAST._IImplMember _2521_genMethod;
              RAST._IImplMember _out93;
              _out93 = (this).GenMethod(_2516_m, true, enclosingType, enclosingTypeParams);
              _2521_genMethod = _out93;
              _2520_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_2520_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_2521_genMethod));
              traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_2519_p, _2520_existing)));
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
      for (BigInteger _2522_i = BigInteger.Zero; _2522_i < _hi22; _2522_i++) {
        DAST._IFormal _2523_param;
        _2523_param = (@params).Select(_2522_i);
        RAST._IType _2524_paramType;
        RAST._IType _out94;
        _out94 = (this).GenType((_2523_param).dtor_typ, false, false);
        _2524_paramType = _out94;
        if ((!((_2524_paramType).CanReadWithoutClone())) && (!((_2523_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _2524_paramType = RAST.Type.create_Borrowed(_2524_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_2523_param).dtor_name), _2524_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _2525_params;
      Dafny.ISequence<RAST._IFormal> _out95;
      _out95 = (this).GenParams((m).dtor_params);
      _2525_params = _out95;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2526_paramNames;
      _2526_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2527_paramTypes;
      _2527_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi23 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _2528_paramI = BigInteger.Zero; _2528_paramI < _hi23; _2528_paramI++) {
        DAST._IFormal _2529_dafny__formal;
        _2529_dafny__formal = ((m).dtor_params).Select(_2528_paramI);
        RAST._IFormal _2530_formal;
        _2530_formal = (_2525_params).Select(_2528_paramI);
        Dafny.ISequence<Dafny.Rune> _2531_name;
        _2531_name = (_2530_formal).dtor_name;
        _2526_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2526_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2531_name));
        _2527_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2527_paramTypes, _2531_name, (_2530_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _2532_fnName;
      _2532_fnName = DCOMP.__default.escapeName((m).dtor_name);
      Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2533_selfIdentifier;
      _2533_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _2534_selfId;
        _2534_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((_2532_fnName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_ctor"))) {
          _2534_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        if (forTrait) {
          RAST._IFormal _2535_selfFormal;
          _2535_selfFormal = RAST.Formal.selfBorrowedMut;
          _2525_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_2535_selfFormal), _2525_params);
        } else {
          RAST._IType _2536_tpe;
          RAST._IType _out96;
          _out96 = (this).GenType(enclosingType, false, false);
          _2536_tpe = _out96;
          if (!((_2536_tpe).CanReadWithoutClone())) {
            _2536_tpe = RAST.Type.create_Borrowed(_2536_tpe);
          }
          _2525_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_2534_selfId, _2536_tpe)), _2525_params);
        }
        _2533_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2534_selfId);
      }
      Dafny.ISequence<RAST._IType> _2537_retTypeArgs;
      _2537_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _2538_typeI;
      _2538_typeI = BigInteger.Zero;
      while ((_2538_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _2539_typeExpr;
        RAST._IType _out97;
        _out97 = (this).GenType(((m).dtor_outTypes).Select(_2538_typeI), false, false);
        _2539_typeExpr = _out97;
        _2537_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_2537_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_2539_typeExpr));
        _2538_typeI = (_2538_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _2540_visibility;
      _2540_visibility = RAST.Visibility.create_PUB();
      Dafny.ISequence<DAST._ITypeArgDecl> _2541_typeParamsFiltered;
      _2541_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi24 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _2542_typeParamI = BigInteger.Zero; _2542_typeParamI < _hi24; _2542_typeParamI++) {
        DAST._ITypeArgDecl _2543_typeParam;
        _2543_typeParam = ((m).dtor_typeParams).Select(_2542_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_2543_typeParam).dtor_name)))) {
          _2541_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_2541_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_2543_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _2544_typeParams;
      _2544_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_2541_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi25 = new BigInteger((_2541_typeParamsFiltered).Count);
        for (BigInteger _2545_i = BigInteger.Zero; _2545_i < _hi25; _2545_i++) {
          DAST._IType _2546_typeArg;
          RAST._ITypeParamDecl _2547_rTypeParamDecl;
          DAST._IType _out98;
          RAST._ITypeParamDecl _out99;
          (this).GenTypeParam((_2541_typeParamsFiltered).Select(_2545_i), out _out98, out _out99);
          _2546_typeArg = _out98;
          _2547_rTypeParamDecl = _out99;
          _2544_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_2544_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_2547_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _2548_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _2549_env = DCOMP.Environment.Default();
      RAST._IExpr _2550_preBody;
      _2550_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      if ((m).dtor_hasBody) {
        RAST._IExpr _2551_earlyReturn;
        _2551_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source85 = (m).dtor_outVars;
        if (_source85.is_None) {
        } else {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2552___mcc_h0 = _source85.dtor_value;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2553_outVars = _2552___mcc_h0;
          {
            Dafny.ISequence<RAST._IExpr> _2554_tupleArgs;
            _2554_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi26 = new BigInteger((_2553_outVars).Count);
            for (BigInteger _2555_outI = BigInteger.Zero; _2555_outI < _hi26; _2555_outI++) {
              Dafny.ISequence<Dafny.Rune> _2556_outVar;
              _2556_outVar = (_2553_outVars).Select(_2555_outI);
              RAST._IType _2557_outType;
              RAST._IType _out100;
              _out100 = (this).GenType(((m).dtor_outTypes).Select(_2555_outI), false, false);
              _2557_outType = _out100;
              Dafny.ISequence<Dafny.Rune> _2558_outName;
              _2558_outName = DCOMP.__default.escapeName((_2556_outVar));
              _2526_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2526_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2558_outName));
              RAST._IType _2559_outMaybeType;
              _2559_outMaybeType = (((_2557_outType).CanReadWithoutClone()) ? (_2557_outType) : (RAST.__default.MaybePlaceboType(_2557_outType)));
              _2527_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2527_paramTypes, _2558_outName, _2559_outMaybeType);
              RAST._IExpr _2560_outVarReturn;
              DCOMP._IOwnership _2561___v54;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2562___v55;
              RAST._IExpr _out101;
              DCOMP._IOwnership _out102;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out103;
              (this).GenExpr(DAST.Expression.create_Ident((_2556_outVar)), Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2558_outName), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>, RAST._IType>(_2558_outName, _2559_outMaybeType))), DCOMP.Ownership.create_OwnershipOwned(), out _out101, out _out102, out _out103);
              _2560_outVarReturn = _out101;
              _2561___v54 = _out102;
              _2562___v55 = _out103;
              _2554_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2554_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2560_outVarReturn));
            }
            if ((new BigInteger((_2554_tupleArgs).Count)) == (BigInteger.One)) {
              _2551_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_2554_tupleArgs).Select(BigInteger.Zero)));
            } else {
              _2551_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_2554_tupleArgs)));
            }
          }
        }
        _2549_env = DCOMP.Environment.create(_2526_paramNames, _2527_paramTypes);
        RAST._IExpr _2563_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2564___v56;
        DCOMP._IEnvironment _2565___v57;
        RAST._IExpr _out104;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out105;
        DCOMP._IEnvironment _out106;
        (this).GenStmts((m).dtor_body, _2533_selfIdentifier, _2549_env, true, _2551_earlyReturn, out _out104, out _out105, out _out106);
        _2563_body = _out104;
        _2564___v56 = _out105;
        _2565___v57 = _out106;
        _2548_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_2550_preBody).Then(_2563_body));
      } else {
        _2549_env = DCOMP.Environment.create(_2526_paramNames, _2527_paramTypes);
        _2548_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_2540_visibility, RAST.Fn.create(_2532_fnName, _2544_typeParams, _2525_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_2537_retTypeArgs).Count)) == (BigInteger.One)) ? ((_2537_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_2537_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _2548_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2566_declarations;
      _2566_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _2567_i;
      _2567_i = BigInteger.Zero;
      newEnv = env;
      while ((_2567_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _2568_stmt;
        _2568_stmt = (stmts).Select(_2567_i);
        RAST._IExpr _2569_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2570_recIdents;
        DCOMP._IEnvironment _2571_newEnv2;
        RAST._IExpr _out107;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out108;
        DCOMP._IEnvironment _out109;
        (this).GenStmt(_2568_stmt, selfIdent, newEnv, (isLast) && ((_2567_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out107, out _out108, out _out109);
        _2569_stmtExpr = _out107;
        _2570_recIdents = _out108;
        _2571_newEnv2 = _out109;
        newEnv = _2571_newEnv2;
        DAST._IStatement _source86 = _2568_stmt;
        if (_source86.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _2572___mcc_h0 = _source86.dtor_name;
          DAST._IType _2573___mcc_h1 = _source86.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> _2574___mcc_h2 = _source86.dtor_maybeValue;
          Dafny.ISequence<Dafny.Rune> _2575_name = _2572___mcc_h0;
          {
            _2566_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2566_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_2575_name)));
          }
        } else if (_source86.is_Assign) {
          DAST._IAssignLhs _2576___mcc_h6 = _source86.dtor_lhs;
          DAST._IExpression _2577___mcc_h7 = _source86.dtor_value;
        } else if (_source86.is_If) {
          DAST._IExpression _2578___mcc_h10 = _source86.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _2579___mcc_h11 = _source86.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _2580___mcc_h12 = _source86.dtor_els;
        } else if (_source86.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _2581___mcc_h16 = _source86.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _2582___mcc_h17 = _source86.dtor_body;
        } else if (_source86.is_While) {
          DAST._IExpression _2583___mcc_h20 = _source86.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _2584___mcc_h21 = _source86.dtor_body;
        } else if (_source86.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _2585___mcc_h24 = _source86.dtor_boundName;
          DAST._IType _2586___mcc_h25 = _source86.dtor_boundType;
          DAST._IExpression _2587___mcc_h26 = _source86.dtor_over;
          Dafny.ISequence<DAST._IStatement> _2588___mcc_h27 = _source86.dtor_body;
        } else if (_source86.is_Call) {
          DAST._IExpression _2589___mcc_h32 = _source86.dtor_on;
          DAST._ICallName _2590___mcc_h33 = _source86.dtor_callName;
          Dafny.ISequence<DAST._IType> _2591___mcc_h34 = _source86.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2592___mcc_h35 = _source86.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _2593___mcc_h36 = _source86.dtor_outs;
        } else if (_source86.is_Return) {
          DAST._IExpression _2594___mcc_h42 = _source86.dtor_expr;
        } else if (_source86.is_EarlyReturn) {
        } else if (_source86.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2595___mcc_h44 = _source86.dtor_toLabel;
        } else if (_source86.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _2596___mcc_h46 = _source86.dtor_body;
        } else if (_source86.is_JumpTailCallStart) {
        } else if (_source86.is_Halt) {
        } else {
          DAST._IExpression _2597___mcc_h48 = _source86.dtor_Print_i_a0;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2570_recIdents, _2566_declarations));
        generated = (generated).Then(_2569_stmtExpr);
        _2567_i = (_2567_i) + (BigInteger.One);
      }
    }
    public void GenAssignLhs(DAST._IAssignLhs lhs, RAST._IExpr rhs, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, out RAST._IExpr generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      newEnv = env;
      DAST._IAssignLhs _source87 = lhs;
      if (_source87.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _2598___mcc_h0 = _source87.dtor_ident;
        Dafny.ISequence<Dafny.Rune> _source88 = _2598___mcc_h0;
        Dafny.ISequence<Dafny.Rune> _2599___mcc_h1 = _source88;
        Dafny.ISequence<Dafny.Rune> _2600_id = _2599___mcc_h1;
        {
          Dafny.ISequence<Dafny.Rune> _2601_idRust;
          _2601_idRust = DCOMP.__default.escapeName(_2600_id);
          if (((env).IsBorrowed(_2601_idRust)) || ((env).IsBorrowedMut(_2601_idRust))) {
            generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _2601_idRust), rhs);
          } else {
            generated = RAST.__default.AssignVar(_2601_idRust, rhs);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2601_idRust);
          needsIIFE = false;
        }
      } else if (_source87.is_Select) {
        DAST._IExpression _2602___mcc_h2 = _source87.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _2603___mcc_h3 = _source87.dtor_field;
        Dafny.ISequence<Dafny.Rune> _2604_field = _2603___mcc_h3;
        DAST._IExpression _2605_on = _2602___mcc_h2;
        {
          Dafny.ISequence<Dafny.Rune> _2606_fieldName;
          _2606_fieldName = DCOMP.__default.escapeName(_2604_field);
          RAST._IExpr _2607_onExpr;
          DCOMP._IOwnership _2608_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2609_recIdents;
          RAST._IExpr _out110;
          DCOMP._IOwnership _out111;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out112;
          (this).GenExpr(_2605_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out110, out _out111, out _out112);
          _2607_onExpr = _out110;
          _2608_onOwned = _out111;
          _2609_recIdents = _out112;
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*("), (_2607_onExpr)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _2606_fieldName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()) = ")), (rhs)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";")));
          readIdents = _2609_recIdents;
          needsIIFE = true;
        }
      } else {
        DAST._IExpression _2610___mcc_h4 = _source87.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _2611___mcc_h5 = _source87.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _2612_indices = _2611___mcc_h5;
        DAST._IExpression _2613_on = _2610___mcc_h4;
        {
          RAST._IExpr _2614_onExpr;
          DCOMP._IOwnership _2615_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2616_recIdents;
          RAST._IExpr _out113;
          DCOMP._IOwnership _out114;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out115;
          (this).GenExpr(_2613_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out113, out _out114, out _out115);
          _2614_onExpr = _out113;
          _2615_onOwned = _out114;
          _2616_recIdents = _out115;
          readIdents = _2616_recIdents;
          Dafny.ISequence<Dafny.Rune> _2617_r;
          _2617_r = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          BigInteger _2618_i;
          _2618_i = BigInteger.Zero;
          while ((_2618_i) < (new BigInteger((_2612_indices).Count))) {
            RAST._IExpr _2619_idx;
            DCOMP._IOwnership _2620___v61;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2621_recIdentsIdx;
            RAST._IExpr _out116;
            DCOMP._IOwnership _out117;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out118;
            (this).GenExpr((_2612_indices).Select(_2618_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out116, out _out117, out _out118);
            _2619_idx = _out116;
            _2620___v61 = _out117;
            _2621_recIdentsIdx = _out118;
            _2617_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2617_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let __idx")), Std.Strings.__default.OfNat(_2618_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = <usize as ::dafny_runtime::NumCast>::from(")), (_2619_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap();\n"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2621_recIdentsIdx);
            _2618_i = (_2618_i) + (BigInteger.One);
          }
          _2617_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2617_r, (_2614_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()"));
          _2618_i = BigInteger.Zero;
          while ((_2618_i) < (new BigInteger((_2612_indices).Count))) {
            _2617_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2617_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[__idx")), Std.Strings.__default.OfNat(_2618_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
            _2618_i = (_2618_i) + (BigInteger.One);
          }
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2617_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), (rhs)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n}")));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source89 = stmt;
      if (_source89.is_DeclareVar) {
        Dafny.ISequence<Dafny.Rune> _2622___mcc_h0 = _source89.dtor_name;
        DAST._IType _2623___mcc_h1 = _source89.dtor_typ;
        Std.Wrappers._IOption<DAST._IExpression> _2624___mcc_h2 = _source89.dtor_maybeValue;
        Std.Wrappers._IOption<DAST._IExpression> _source90 = _2624___mcc_h2;
        if (_source90.is_None) {
          DAST._IType _2625_typ = _2623___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _2626_name = _2622___mcc_h0;
          {
            DAST._IStatement _2627_newStmt;
            _2627_newStmt = DAST.Statement.create_DeclareVar(_2626_name, _2625_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_2625_typ)));
            RAST._IExpr _out119;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out120;
            DCOMP._IEnvironment _out121;
            (this).GenStmt(_2627_newStmt, selfIdent, env, isLast, earlyReturn, out _out119, out _out120, out _out121);
            generated = _out119;
            readIdents = _out120;
            newEnv = _out121;
          }
        } else {
          DAST._IExpression _2628___mcc_h3 = _source90.dtor_value;
          DAST._IExpression _2629_expression = _2628___mcc_h3;
          DAST._IType _2630_typ = _2623___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _2631_name = _2622___mcc_h0;
          {
            RAST._IType _2632_tpe;
            RAST._IType _out122;
            _out122 = (this).GenType(_2630_typ, true, false);
            _2632_tpe = _out122;
            Dafny.ISequence<Dafny.Rune> _2633_varName;
            _2633_varName = DCOMP.__default.escapeName(_2631_name);
            bool _2634_hasCopySemantics;
            _2634_hasCopySemantics = (_2632_tpe).CanReadWithoutClone();
            if (((_2629_expression).is_InitializationValue) && (!(_2634_hasCopySemantics))) {
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2633_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).ApplyType1(_2632_tpe)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              newEnv = (env).AddAssigned(_2633_varName, RAST.__default.MaybePlaceboType(_2632_tpe));
            } else {
              RAST._IExpr _2635_expr = RAST.Expr.Default();
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2636_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
              DCOMP._IOwnership _2637_exprOwnership = DCOMP.Ownership.Default();
              RAST._IExpr _out123;
              DCOMP._IOwnership _out124;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out125;
              (this).GenExpr(_2629_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out123, out _out124, out _out125);
              _2635_expr = _out123;
              _2637_exprOwnership = _out124;
              _2636_recIdents = _out125;
              readIdents = _2636_recIdents;
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_2631_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2632_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2635_expr));
              newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_2631_name), _2632_tpe);
            }
          }
        }
      } else if (_source89.is_Assign) {
        DAST._IAssignLhs _2638___mcc_h4 = _source89.dtor_lhs;
        DAST._IExpression _2639___mcc_h5 = _source89.dtor_value;
        DAST._IExpression _2640_expression = _2639___mcc_h5;
        DAST._IAssignLhs _2641_lhs = _2638___mcc_h4;
        {
          RAST._IExpr _2642_exprGen;
          DCOMP._IOwnership _2643___v62;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2644_exprIdents;
          RAST._IExpr _out126;
          DCOMP._IOwnership _out127;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out128;
          (this).GenExpr(_2640_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out126, out _out127, out _out128);
          _2642_exprGen = _out126;
          _2643___v62 = _out127;
          _2644_exprIdents = _out128;
          if ((_2641_lhs).is_Ident) {
            Dafny.ISequence<Dafny.Rune> _2645_rustId;
            _2645_rustId = DCOMP.__default.escapeName(((_2641_lhs).dtor_ident));
            Std.Wrappers._IOption<RAST._IType> _2646_tpe;
            _2646_tpe = (env).GetType(_2645_rustId);
            if (((_2646_tpe).is_Some) && ((((_2646_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
              _2642_exprGen = RAST.__default.MaybePlacebo(_2642_exprGen);
            }
          }
          RAST._IExpr _2647_lhsGen;
          bool _2648_needsIIFE;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2649_recIdents;
          DCOMP._IEnvironment _2650_resEnv;
          RAST._IExpr _out129;
          bool _out130;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
          DCOMP._IEnvironment _out132;
          (this).GenAssignLhs(_2641_lhs, _2642_exprGen, selfIdent, env, out _out129, out _out130, out _out131, out _out132);
          _2647_lhsGen = _out129;
          _2648_needsIIFE = _out130;
          _2649_recIdents = _out131;
          _2650_resEnv = _out132;
          generated = _2647_lhsGen;
          newEnv = _2650_resEnv;
          if (_2648_needsIIFE) {
            generated = RAST.Expr.create_Block(generated);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2649_recIdents, _2644_exprIdents);
        }
      } else if (_source89.is_If) {
        DAST._IExpression _2651___mcc_h6 = _source89.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _2652___mcc_h7 = _source89.dtor_thn;
        Dafny.ISequence<DAST._IStatement> _2653___mcc_h8 = _source89.dtor_els;
        Dafny.ISequence<DAST._IStatement> _2654_elsDafny = _2653___mcc_h8;
        Dafny.ISequence<DAST._IStatement> _2655_thnDafny = _2652___mcc_h7;
        DAST._IExpression _2656_cond = _2651___mcc_h6;
        {
          RAST._IExpr _2657_cond;
          DCOMP._IOwnership _2658___v63;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2659_recIdents;
          RAST._IExpr _out133;
          DCOMP._IOwnership _out134;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
          (this).GenExpr(_2656_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out133, out _out134, out _out135);
          _2657_cond = _out133;
          _2658___v63 = _out134;
          _2659_recIdents = _out135;
          Dafny.ISequence<Dafny.Rune> _2660_condString;
          _2660_condString = (_2657_cond)._ToString(DCOMP.__default.IND);
          readIdents = _2659_recIdents;
          RAST._IExpr _2661_thn;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2662_thnIdents;
          DCOMP._IEnvironment _2663_thnEnv;
          RAST._IExpr _out136;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
          DCOMP._IEnvironment _out138;
          (this).GenStmts(_2655_thnDafny, selfIdent, env, isLast, earlyReturn, out _out136, out _out137, out _out138);
          _2661_thn = _out136;
          _2662_thnIdents = _out137;
          _2663_thnEnv = _out138;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2662_thnIdents);
          RAST._IExpr _2664_els;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2665_elsIdents;
          DCOMP._IEnvironment _2666_elsEnv;
          RAST._IExpr _out139;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out140;
          DCOMP._IEnvironment _out141;
          (this).GenStmts(_2654_elsDafny, selfIdent, env, isLast, earlyReturn, out _out139, out _out140, out _out141);
          _2664_els = _out139;
          _2665_elsIdents = _out140;
          _2666_elsEnv = _out141;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2665_elsIdents);
          newEnv = env;
          generated = RAST.Expr.create_IfExpr(_2657_cond, _2661_thn, _2664_els);
        }
      } else if (_source89.is_Labeled) {
        Dafny.ISequence<Dafny.Rune> _2667___mcc_h9 = _source89.dtor_lbl;
        Dafny.ISequence<DAST._IStatement> _2668___mcc_h10 = _source89.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2669_body = _2668___mcc_h10;
        Dafny.ISequence<Dafny.Rune> _2670_lbl = _2667___mcc_h9;
        {
          RAST._IExpr _2671_body;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2672_bodyIdents;
          DCOMP._IEnvironment _2673_env2;
          RAST._IExpr _out142;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out143;
          DCOMP._IEnvironment _out144;
          (this).GenStmts(_2669_body, selfIdent, env, isLast, earlyReturn, out _out142, out _out143, out _out144);
          _2671_body = _out142;
          _2672_bodyIdents = _out143;
          _2673_env2 = _out144;
          readIdents = _2672_bodyIdents;
          generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _2670_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_2671_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
          newEnv = env;
        }
      } else if (_source89.is_While) {
        DAST._IExpression _2674___mcc_h11 = _source89.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _2675___mcc_h12 = _source89.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2676_body = _2675___mcc_h12;
        DAST._IExpression _2677_cond = _2674___mcc_h11;
        {
          RAST._IExpr _2678_cond;
          DCOMP._IOwnership _2679___v64;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2680_recIdents;
          RAST._IExpr _out145;
          DCOMP._IOwnership _out146;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out147;
          (this).GenExpr(_2677_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out145, out _out146, out _out147);
          _2678_cond = _out145;
          _2679___v64 = _out146;
          _2680_recIdents = _out147;
          readIdents = _2680_recIdents;
          RAST._IExpr _2681_bodyExpr;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2682_bodyIdents;
          DCOMP._IEnvironment _2683_bodyEnv;
          RAST._IExpr _out148;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out149;
          DCOMP._IEnvironment _out150;
          (this).GenStmts(_2676_body, selfIdent, env, false, earlyReturn, out _out148, out _out149, out _out150);
          _2681_bodyExpr = _out148;
          _2682_bodyIdents = _out149;
          _2683_bodyEnv = _out150;
          newEnv = env;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2682_bodyIdents);
          generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_2678_cond), _2681_bodyExpr);
        }
      } else if (_source89.is_Foreach) {
        Dafny.ISequence<Dafny.Rune> _2684___mcc_h13 = _source89.dtor_boundName;
        DAST._IType _2685___mcc_h14 = _source89.dtor_boundType;
        DAST._IExpression _2686___mcc_h15 = _source89.dtor_over;
        Dafny.ISequence<DAST._IStatement> _2687___mcc_h16 = _source89.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2688_body = _2687___mcc_h16;
        DAST._IExpression _2689_over = _2686___mcc_h15;
        DAST._IType _2690_boundType = _2685___mcc_h14;
        Dafny.ISequence<Dafny.Rune> _2691_boundName = _2684___mcc_h13;
        {
          RAST._IExpr _2692_over;
          DCOMP._IOwnership _2693___v65;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2694_recIdents;
          RAST._IExpr _out151;
          DCOMP._IOwnership _out152;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out153;
          (this).GenExpr(_2689_over, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out151, out _out152, out _out153);
          _2692_over = _out151;
          _2693___v65 = _out152;
          _2694_recIdents = _out153;
          RAST._IType _2695_boundTpe;
          RAST._IType _out154;
          _out154 = (this).GenType(_2690_boundType, false, false);
          _2695_boundTpe = _out154;
          readIdents = _2694_recIdents;
          Dafny.ISequence<Dafny.Rune> _2696_boundRName;
          _2696_boundRName = DCOMP.__default.escapeName(_2691_boundName);
          RAST._IExpr _2697_bodyExpr;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2698_bodyIdents;
          DCOMP._IEnvironment _2699_bodyEnv;
          RAST._IExpr _out155;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
          DCOMP._IEnvironment _out157;
          (this).GenStmts(_2688_body, selfIdent, (env).AddAssigned(_2696_boundRName, _2695_boundTpe), false, earlyReturn, out _out155, out _out156, out _out157);
          _2697_bodyExpr = _out155;
          _2698_bodyIdents = _out156;
          _2699_bodyEnv = _out157;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2698_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2696_boundRName));
          newEnv = env;
          generated = RAST.Expr.create_For(_2696_boundRName, _2692_over, _2697_bodyExpr);
        }
      } else if (_source89.is_Call) {
        DAST._IExpression _2700___mcc_h17 = _source89.dtor_on;
        DAST._ICallName _2701___mcc_h18 = _source89.dtor_callName;
        Dafny.ISequence<DAST._IType> _2702___mcc_h19 = _source89.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _2703___mcc_h20 = _source89.dtor_args;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _2704___mcc_h21 = _source89.dtor_outs;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _2705_maybeOutVars = _2704___mcc_h21;
        Dafny.ISequence<DAST._IExpression> _2706_args = _2703___mcc_h20;
        Dafny.ISequence<DAST._IType> _2707_typeArgs = _2702___mcc_h19;
        DAST._ICallName _2708_name = _2701___mcc_h18;
        DAST._IExpression _2709_on = _2700___mcc_h17;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          RAST._IExpr _2710_onExpr;
          DCOMP._IOwnership _2711___v68;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2712_enclosingIdents;
          RAST._IExpr _out158;
          DCOMP._IOwnership _out159;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out160;
          (this).GenExpr(_2709_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out158, out _out159, out _out160);
          _2710_onExpr = _out158;
          _2711___v68 = _out159;
          _2712_enclosingIdents = _out160;
          Dafny.ISequence<RAST._IType> _2713_typeExprs;
          _2713_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
          if ((new BigInteger((_2707_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _2714_typeI;
            _2714_typeI = BigInteger.Zero;
            Dafny.ISequence<RAST._IType> _2715_typeArgsR;
            _2715_typeArgsR = Dafny.Sequence<RAST._IType>.FromElements();
            while ((_2714_typeI) < (new BigInteger((_2707_typeArgs).Count))) {
              RAST._IType _2716_tpe;
              RAST._IType _out161;
              _out161 = (this).GenType((_2707_typeArgs).Select(_2714_typeI), false, false);
              _2716_tpe = _out161;
              _2715_typeArgsR = Dafny.Sequence<RAST._IType>.Concat(_2715_typeArgsR, Dafny.Sequence<RAST._IType>.FromElements(_2716_tpe));
              _2714_typeI = (_2714_typeI) + (BigInteger.One);
            }
          }
          Dafny.ISequence<RAST._IExpr> _2717_argExprs;
          _2717_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi27 = new BigInteger((_2706_args).Count);
          for (BigInteger _2718_i = BigInteger.Zero; _2718_i < _hi27; _2718_i++) {
            DCOMP._IOwnership _2719_argOwnership;
            _2719_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            if (((_2708_name).is_CallName) && ((_2718_i) < (new BigInteger((((_2708_name).dtor_signature)).Count)))) {
              RAST._IType _2720_tpe;
              RAST._IType _out162;
              _out162 = (this).GenType(((((_2708_name).dtor_signature)).Select(_2718_i)).dtor_typ, false, false);
              _2720_tpe = _out162;
              if ((_2720_tpe).CanReadWithoutClone()) {
                _2719_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
              }
            }
            RAST._IExpr _2721_argExpr;
            DCOMP._IOwnership _2722_ownership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2723_argIdents;
            RAST._IExpr _out163;
            DCOMP._IOwnership _out164;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out165;
            (this).GenExpr((_2706_args).Select(_2718_i), selfIdent, env, _2719_argOwnership, out _out163, out _out164, out _out165);
            _2721_argExpr = _out163;
            _2722_ownership = _out164;
            _2723_argIdents = _out165;
            _2717_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_2717_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_2721_argExpr));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2723_argIdents);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2712_enclosingIdents);
          Dafny.ISequence<Dafny.Rune> _2724_renderedName;
          _2724_renderedName = ((System.Func<DAST._ICallName, Dafny.ISequence<Dafny.Rune>>)((_source91) => {
            if (_source91.is_CallName) {
              Dafny.ISequence<Dafny.Rune> _2725___mcc_h26 = _source91.dtor_name;
              Std.Wrappers._IOption<DAST._IType> _2726___mcc_h27 = _source91.dtor_onType;
              Dafny.ISequence<DAST._IFormal> _2727___mcc_h28 = _source91.dtor_signature;
              Dafny.ISequence<Dafny.Rune> _2728_name = _2725___mcc_h26;
              return DCOMP.__default.escapeName(_2728_name);
            } else if (_source91.is_MapBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else if (_source91.is_MapBuilderBuild) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            } else if (_source91.is_SetBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            }
          }))(_2708_name);
          DAST._IExpression _source92 = _2709_on;
          if (_source92.is_Literal) {
            DAST._ILiteral _2729___mcc_h29 = _source92.dtor_Literal_i_a0;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _2730___mcc_h31 = _source92.dtor_Ident_i_a0;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2731___mcc_h33 = _source92.dtor_Companion_i_a0;
            {
              _2710_onExpr = (_2710_onExpr).MSel(_2724_renderedName);
            }
          } else if (_source92.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _2732___mcc_h35 = _source92.dtor_Tuple_i_a0;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2733___mcc_h37 = _source92.dtor_path;
            Dafny.ISequence<DAST._IType> _2734___mcc_h38 = _source92.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _2735___mcc_h39 = _source92.dtor_args;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _2736___mcc_h43 = _source92.dtor_dims;
            DAST._IType _2737___mcc_h44 = _source92.dtor_typ;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_DatatypeValue) {
            DAST._IDatatypeType _2738___mcc_h47 = _source92.dtor_datatypeType;
            Dafny.ISequence<DAST._IType> _2739___mcc_h48 = _source92.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _2740___mcc_h49 = _source92.dtor_variant;
            bool _2741___mcc_h50 = _source92.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2742___mcc_h51 = _source92.dtor_contents;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_Convert) {
            DAST._IExpression _2743___mcc_h57 = _source92.dtor_value;
            DAST._IType _2744___mcc_h58 = _source92.dtor_from;
            DAST._IType _2745___mcc_h59 = _source92.dtor_typ;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_SeqConstruct) {
            DAST._IExpression _2746___mcc_h63 = _source92.dtor_length;
            DAST._IExpression _2747___mcc_h64 = _source92.dtor_elem;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _2748___mcc_h67 = _source92.dtor_elements;
            DAST._IType _2749___mcc_h68 = _source92.dtor_typ;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _2750___mcc_h71 = _source92.dtor_elements;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_MultisetValue) {
            Dafny.ISequence<DAST._IExpression> _2751___mcc_h73 = _source92.dtor_elements;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_MapValue) {
            Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2752___mcc_h75 = _source92.dtor_mapElems;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_MapBuilder) {
            DAST._IType _2753___mcc_h77 = _source92.dtor_keyType;
            DAST._IType _2754___mcc_h78 = _source92.dtor_valueType;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_SeqUpdate) {
            DAST._IExpression _2755___mcc_h81 = _source92.dtor_expr;
            DAST._IExpression _2756___mcc_h82 = _source92.dtor_indexExpr;
            DAST._IExpression _2757___mcc_h83 = _source92.dtor_value;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_MapUpdate) {
            DAST._IExpression _2758___mcc_h87 = _source92.dtor_expr;
            DAST._IExpression _2759___mcc_h88 = _source92.dtor_indexExpr;
            DAST._IExpression _2760___mcc_h89 = _source92.dtor_value;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_SetBuilder) {
            DAST._IType _2761___mcc_h93 = _source92.dtor_elemType;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_ToMultiset) {
            DAST._IExpression _2762___mcc_h95 = _source92.dtor_ToMultiset_i_a0;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_This) {
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_Ite) {
            DAST._IExpression _2763___mcc_h97 = _source92.dtor_cond;
            DAST._IExpression _2764___mcc_h98 = _source92.dtor_thn;
            DAST._IExpression _2765___mcc_h99 = _source92.dtor_els;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_UnOp) {
            DAST._IUnaryOp _2766___mcc_h103 = _source92.dtor_unOp;
            DAST._IExpression _2767___mcc_h104 = _source92.dtor_expr;
            DAST.Format._IUnaryOpFormat _2768___mcc_h105 = _source92.dtor_format1;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_BinOp) {
            DAST._IBinOp _2769___mcc_h109 = _source92.dtor_op;
            DAST._IExpression _2770___mcc_h110 = _source92.dtor_left;
            DAST._IExpression _2771___mcc_h111 = _source92.dtor_right;
            DAST.Format._IBinaryOpFormat _2772___mcc_h112 = _source92.dtor_format2;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_ArrayLen) {
            DAST._IExpression _2773___mcc_h117 = _source92.dtor_expr;
            BigInteger _2774___mcc_h118 = _source92.dtor_dim;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_MapKeys) {
            DAST._IExpression _2775___mcc_h121 = _source92.dtor_expr;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_MapValues) {
            DAST._IExpression _2776___mcc_h123 = _source92.dtor_expr;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_Select) {
            DAST._IExpression _2777___mcc_h125 = _source92.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2778___mcc_h126 = _source92.dtor_field;
            bool _2779___mcc_h127 = _source92.dtor_isConstant;
            bool _2780___mcc_h128 = _source92.dtor_onDatatype;
            DAST._IType _2781___mcc_h129 = _source92.dtor_fieldType;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_SelectFn) {
            DAST._IExpression _2782___mcc_h135 = _source92.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2783___mcc_h136 = _source92.dtor_field;
            bool _2784___mcc_h137 = _source92.dtor_onDatatype;
            bool _2785___mcc_h138 = _source92.dtor_isStatic;
            BigInteger _2786___mcc_h139 = _source92.dtor_arity;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_Index) {
            DAST._IExpression _2787___mcc_h145 = _source92.dtor_expr;
            DAST._ICollKind _2788___mcc_h146 = _source92.dtor_collKind;
            Dafny.ISequence<DAST._IExpression> _2789___mcc_h147 = _source92.dtor_indices;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_IndexRange) {
            DAST._IExpression _2790___mcc_h151 = _source92.dtor_expr;
            bool _2791___mcc_h152 = _source92.dtor_isArray;
            Std.Wrappers._IOption<DAST._IExpression> _2792___mcc_h153 = _source92.dtor_low;
            Std.Wrappers._IOption<DAST._IExpression> _2793___mcc_h154 = _source92.dtor_high;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_TupleSelect) {
            DAST._IExpression _2794___mcc_h159 = _source92.dtor_expr;
            BigInteger _2795___mcc_h160 = _source92.dtor_index;
            DAST._IType _2796___mcc_h161 = _source92.dtor_fieldType;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_Call) {
            DAST._IExpression _2797___mcc_h165 = _source92.dtor_on;
            DAST._ICallName _2798___mcc_h166 = _source92.dtor_callName;
            Dafny.ISequence<DAST._IType> _2799___mcc_h167 = _source92.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _2800___mcc_h168 = _source92.dtor_args;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2801___mcc_h173 = _source92.dtor_params;
            DAST._IType _2802___mcc_h174 = _source92.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _2803___mcc_h175 = _source92.dtor_body;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2804___mcc_h179 = _source92.dtor_values;
            DAST._IType _2805___mcc_h180 = _source92.dtor_retType;
            DAST._IExpression _2806___mcc_h181 = _source92.dtor_expr;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _2807___mcc_h185 = _source92.dtor_name;
            DAST._IType _2808___mcc_h186 = _source92.dtor_typ;
            DAST._IExpression _2809___mcc_h187 = _source92.dtor_value;
            DAST._IExpression _2810___mcc_h188 = _source92.dtor_iifeBody;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_Apply) {
            DAST._IExpression _2811___mcc_h193 = _source92.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _2812___mcc_h194 = _source92.dtor_args;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_TypeTest) {
            DAST._IExpression _2813___mcc_h197 = _source92.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2814___mcc_h198 = _source92.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _2815___mcc_h199 = _source92.dtor_variant;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_InitializationValue) {
            DAST._IType _2816___mcc_h203 = _source92.dtor_typ;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_BoolBoundedPool) {
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_SetBoundedPool) {
            DAST._IExpression _2817___mcc_h205 = _source92.dtor_of;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_SeqBoundedPool) {
            DAST._IExpression _2818___mcc_h207 = _source92.dtor_of;
            bool _2819___mcc_h208 = _source92.dtor_includeDuplicates;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else {
            DAST._IExpression _2820___mcc_h211 = _source92.dtor_lo;
            DAST._IExpression _2821___mcc_h212 = _source92.dtor_hi;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          }
          generated = _2710_onExpr;
          if ((new BigInteger((_2713_typeExprs).Count)).Sign == 1) {
            generated = (generated).ApplyType(_2713_typeExprs);
          }
          generated = (generated).Apply(_2717_argExprs);
          if (((_2705_maybeOutVars).is_Some) && ((new BigInteger(((_2705_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
            Dafny.ISequence<Dafny.Rune> _2822_outVar;
            _2822_outVar = DCOMP.__default.escapeName((((_2705_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
            if (!((env).CanReadWithoutClone(_2822_outVar))) {
              generated = RAST.__default.MaybePlacebo(generated);
            }
            generated = RAST.__default.AssignVar(_2822_outVar, generated);
          } else if (((_2705_maybeOutVars).is_None) || ((new BigInteger(((_2705_maybeOutVars).dtor_value).Count)).Sign == 0)) {
          } else {
            Dafny.ISequence<Dafny.Rune> _2823_tmpVar;
            _2823_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
            RAST._IExpr _2824_tmpId;
            _2824_tmpId = RAST.Expr.create_Identifier(_2823_tmpVar);
            generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _2823_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2825_outVars;
            _2825_outVars = (_2705_maybeOutVars).dtor_value;
            BigInteger _hi28 = new BigInteger((_2825_outVars).Count);
            for (BigInteger _2826_outI = BigInteger.Zero; _2826_outI < _hi28; _2826_outI++) {
              Dafny.ISequence<Dafny.Rune> _2827_outVar;
              _2827_outVar = DCOMP.__default.escapeName(((_2825_outVars).Select(_2826_outI)));
              RAST._IExpr _2828_rhs;
              _2828_rhs = (_2824_tmpId).Sel(Std.Strings.__default.OfNat(_2826_outI));
              if (!((env).CanReadWithoutClone(_2827_outVar))) {
                _2828_rhs = RAST.__default.MaybePlacebo(_2828_rhs);
              }
              generated = (generated).Then(RAST.__default.AssignVar(_2827_outVar, _2828_rhs));
            }
          }
          newEnv = env;
        }
      } else if (_source89.is_Return) {
        DAST._IExpression _2829___mcc_h22 = _source89.dtor_expr;
        DAST._IExpression _2830_exprDafny = _2829___mcc_h22;
        {
          RAST._IExpr _2831_expr;
          DCOMP._IOwnership _2832___v73;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2833_recIdents;
          RAST._IExpr _out166;
          DCOMP._IOwnership _out167;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out168;
          (this).GenExpr(_2830_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out166, out _out167, out _out168);
          _2831_expr = _out166;
          _2832___v73 = _out167;
          _2833_recIdents = _out168;
          readIdents = _2833_recIdents;
          if (isLast) {
            generated = _2831_expr;
          } else {
            generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_2831_expr));
          }
          newEnv = env;
        }
      } else if (_source89.is_EarlyReturn) {
        {
          generated = earlyReturn;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
      } else if (_source89.is_Break) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2834___mcc_h23 = _source89.dtor_toLabel;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2835_toLabel = _2834___mcc_h23;
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source93 = _2835_toLabel;
          if (_source93.is_None) {
            {
              generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2836___mcc_h215 = _source93.dtor_value;
            Dafny.ISequence<Dafny.Rune> _2837_lbl = _2836___mcc_h215;
            {
              generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _2837_lbl)));
            }
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
      } else if (_source89.is_TailRecursive) {
        Dafny.ISequence<DAST._IStatement> _2838___mcc_h24 = _source89.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2839_body = _2838___mcc_h24;
        {
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
            generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
          }
          newEnv = env;
          BigInteger _hi29 = new BigInteger(((env).dtor_names).Count);
          for (BigInteger _2840_paramI = BigInteger.Zero; _2840_paramI < _hi29; _2840_paramI++) {
            Dafny.ISequence<Dafny.Rune> _2841_param;
            _2841_param = ((env).dtor_names).Select(_2840_paramI);
            RAST._IExpr _2842_paramInit;
            DCOMP._IOwnership _2843___v66;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2844___v67;
            RAST._IExpr _out169;
            DCOMP._IOwnership _out170;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out171;
            (this).GenIdent(_2841_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out169, out _out170, out _out171);
            _2842_paramInit = _out169;
            _2843___v66 = _out170;
            _2844___v67 = _out171;
            generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2841_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2842_paramInit)));
            if (((env).dtor_types).Contains(_2841_param)) {
              RAST._IType _2845_declaredType;
              _2845_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_2841_param)).ToOwned();
              newEnv = (newEnv).AddAssigned(_2841_param, _2845_declaredType);
            }
          }
          RAST._IExpr _2846_bodyExpr;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2847_bodyIdents;
          DCOMP._IEnvironment _2848_bodyEnv;
          RAST._IExpr _out172;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out173;
          DCOMP._IEnvironment _out174;
          (this).GenStmts(_2839_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), newEnv, false, earlyReturn, out _out172, out _out173, out _out174);
          _2846_bodyExpr = _out172;
          _2847_bodyIdents = _out173;
          _2848_bodyEnv = _out174;
          readIdents = _2847_bodyIdents;
          generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _2846_bodyExpr)));
        }
      } else if (_source89.is_JumpTailCallStart) {
        {
          generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
      } else if (_source89.is_Halt) {
        {
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
      } else {
        DAST._IExpression _2849___mcc_h25 = _source89.dtor_Print_i_a0;
        DAST._IExpression _2850_e = _2849___mcc_h25;
        {
          RAST._IExpr _2851_printedExpr;
          DCOMP._IOwnership _2852_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2853_recIdents;
          RAST._IExpr _out175;
          DCOMP._IOwnership _out176;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
          (this).GenExpr(_2850_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out175, out _out176, out _out177);
          _2851_printedExpr = _out175;
          _2852_recOwnership = _out176;
          _2853_recIdents = _out177;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_2851_printedExpr)));
          readIdents = _2853_recIdents;
          newEnv = env;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source94 = range;
      if (_source94.is_U8) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
      } else if (_source94.is_I8) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
      } else if (_source94.is_U16) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
      } else if (_source94.is_I16) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
      } else if (_source94.is_U32) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
      } else if (_source94.is_I32) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
      } else if (_source94.is_U64) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
      } else if (_source94.is_I64) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
      } else if (_source94.is_U128) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
      } else if (_source94.is_I128) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
      } else if (_source94.is_BigInt) {
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
      DAST._IExpression _source95 = e;
      DAST._ILiteral _2854___mcc_h0 = _source95.dtor_Literal_i_a0;
      DAST._ILiteral _source96 = _2854___mcc_h0;
      if (_source96.is_BoolLiteral) {
        bool _2855___mcc_h1 = _source96.dtor_BoolLiteral_i_a0;
        bool _2856_b = _2855___mcc_h1;
        {
          RAST._IExpr _out182;
          DCOMP._IOwnership _out183;
          DCOMP.COMP.FromOwned(RAST.Expr.create_LiteralBool(_2856_b), expectedOwnership, out _out182, out _out183);
          r = _out182;
          resultingOwnership = _out183;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source96.is_IntLiteral) {
        Dafny.ISequence<Dafny.Rune> _2857___mcc_h2 = _source96.dtor_IntLiteral_i_a0;
        DAST._IType _2858___mcc_h3 = _source96.dtor_IntLiteral_i_a1;
        DAST._IType _2859_t = _2858___mcc_h3;
        Dafny.ISequence<Dafny.Rune> _2860_i = _2857___mcc_h2;
        {
          DAST._IType _source97 = _2859_t;
          if (_source97.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2861___mcc_h102 = _source97.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _2862___mcc_h103 = _source97.dtor_typeArgs;
            DAST._IResolvedType _2863___mcc_h104 = _source97.dtor_resolved;
            DAST._IType _2864_o = _2859_t;
            {
              RAST._IType _2865_genType;
              RAST._IType _out184;
              _out184 = (this).GenType(_2864_o, false, false);
              _2865_genType = _out184;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2860_i), _2865_genType);
            }
          } else if (_source97.is_Nullable) {
            DAST._IType _2866___mcc_h108 = _source97.dtor_Nullable_i_a0;
            DAST._IType _2867_o = _2859_t;
            {
              RAST._IType _2868_genType;
              RAST._IType _out185;
              _out185 = (this).GenType(_2867_o, false, false);
              _2868_genType = _out185;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2860_i), _2868_genType);
            }
          } else if (_source97.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2869___mcc_h110 = _source97.dtor_Tuple_i_a0;
            DAST._IType _2870_o = _2859_t;
            {
              RAST._IType _2871_genType;
              RAST._IType _out186;
              _out186 = (this).GenType(_2870_o, false, false);
              _2871_genType = _out186;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2860_i), _2871_genType);
            }
          } else if (_source97.is_Array) {
            DAST._IType _2872___mcc_h112 = _source97.dtor_element;
            BigInteger _2873___mcc_h113 = _source97.dtor_dims;
            DAST._IType _2874_o = _2859_t;
            {
              RAST._IType _2875_genType;
              RAST._IType _out187;
              _out187 = (this).GenType(_2874_o, false, false);
              _2875_genType = _out187;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2860_i), _2875_genType);
            }
          } else if (_source97.is_Seq) {
            DAST._IType _2876___mcc_h116 = _source97.dtor_element;
            DAST._IType _2877_o = _2859_t;
            {
              RAST._IType _2878_genType;
              RAST._IType _out188;
              _out188 = (this).GenType(_2877_o, false, false);
              _2878_genType = _out188;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2860_i), _2878_genType);
            }
          } else if (_source97.is_Set) {
            DAST._IType _2879___mcc_h118 = _source97.dtor_element;
            DAST._IType _2880_o = _2859_t;
            {
              RAST._IType _2881_genType;
              RAST._IType _out189;
              _out189 = (this).GenType(_2880_o, false, false);
              _2881_genType = _out189;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2860_i), _2881_genType);
            }
          } else if (_source97.is_Multiset) {
            DAST._IType _2882___mcc_h120 = _source97.dtor_element;
            DAST._IType _2883_o = _2859_t;
            {
              RAST._IType _2884_genType;
              RAST._IType _out190;
              _out190 = (this).GenType(_2883_o, false, false);
              _2884_genType = _out190;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2860_i), _2884_genType);
            }
          } else if (_source97.is_Map) {
            DAST._IType _2885___mcc_h122 = _source97.dtor_key;
            DAST._IType _2886___mcc_h123 = _source97.dtor_value;
            DAST._IType _2887_o = _2859_t;
            {
              RAST._IType _2888_genType;
              RAST._IType _out191;
              _out191 = (this).GenType(_2887_o, false, false);
              _2888_genType = _out191;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2860_i), _2888_genType);
            }
          } else if (_source97.is_SetBuilder) {
            DAST._IType _2889___mcc_h126 = _source97.dtor_element;
            DAST._IType _2890_o = _2859_t;
            {
              RAST._IType _2891_genType;
              RAST._IType _out192;
              _out192 = (this).GenType(_2890_o, false, false);
              _2891_genType = _out192;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2860_i), _2891_genType);
            }
          } else if (_source97.is_MapBuilder) {
            DAST._IType _2892___mcc_h128 = _source97.dtor_key;
            DAST._IType _2893___mcc_h129 = _source97.dtor_value;
            DAST._IType _2894_o = _2859_t;
            {
              RAST._IType _2895_genType;
              RAST._IType _out193;
              _out193 = (this).GenType(_2894_o, false, false);
              _2895_genType = _out193;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2860_i), _2895_genType);
            }
          } else if (_source97.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2896___mcc_h132 = _source97.dtor_args;
            DAST._IType _2897___mcc_h133 = _source97.dtor_result;
            DAST._IType _2898_o = _2859_t;
            {
              RAST._IType _2899_genType;
              RAST._IType _out194;
              _out194 = (this).GenType(_2898_o, false, false);
              _2899_genType = _out194;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2860_i), _2899_genType);
            }
          } else if (_source97.is_Primitive) {
            DAST._IPrimitive _2900___mcc_h136 = _source97.dtor_Primitive_i_a0;
            DAST._IPrimitive _source98 = _2900___mcc_h136;
            if (_source98.is_Int) {
              {
                if ((new BigInteger((_2860_i).Count)) <= (new BigInteger(4))) {
                  r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_2860_i));
                } else {
                  r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_2860_i, true));
                }
              }
            } else if (_source98.is_Real) {
              DAST._IType _2901_o = _2859_t;
              {
                RAST._IType _2902_genType;
                RAST._IType _out195;
                _out195 = (this).GenType(_2901_o, false, false);
                _2902_genType = _out195;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2860_i), _2902_genType);
              }
            } else if (_source98.is_String) {
              DAST._IType _2903_o = _2859_t;
              {
                RAST._IType _2904_genType;
                RAST._IType _out196;
                _out196 = (this).GenType(_2903_o, false, false);
                _2904_genType = _out196;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2860_i), _2904_genType);
              }
            } else if (_source98.is_Bool) {
              DAST._IType _2905_o = _2859_t;
              {
                RAST._IType _2906_genType;
                RAST._IType _out197;
                _out197 = (this).GenType(_2905_o, false, false);
                _2906_genType = _out197;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2860_i), _2906_genType);
              }
            } else {
              DAST._IType _2907_o = _2859_t;
              {
                RAST._IType _2908_genType;
                RAST._IType _out198;
                _out198 = (this).GenType(_2907_o, false, false);
                _2908_genType = _out198;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2860_i), _2908_genType);
              }
            }
          } else if (_source97.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2909___mcc_h138 = _source97.dtor_Passthrough_i_a0;
            DAST._IType _2910_o = _2859_t;
            {
              RAST._IType _2911_genType;
              RAST._IType _out199;
              _out199 = (this).GenType(_2910_o, false, false);
              _2911_genType = _out199;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2860_i), _2911_genType);
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2912___mcc_h140 = _source97.dtor_TypeArg_i_a0;
            DAST._IType _2913_o = _2859_t;
            {
              RAST._IType _2914_genType;
              RAST._IType _out200;
              _out200 = (this).GenType(_2913_o, false, false);
              _2914_genType = _out200;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2860_i), _2914_genType);
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
      } else if (_source96.is_DecLiteral) {
        Dafny.ISequence<Dafny.Rune> _2915___mcc_h4 = _source96.dtor_DecLiteral_i_a0;
        Dafny.ISequence<Dafny.Rune> _2916___mcc_h5 = _source96.dtor_DecLiteral_i_a1;
        DAST._IType _2917___mcc_h6 = _source96.dtor_DecLiteral_i_a2;
        DAST._IType _2918_t = _2917___mcc_h6;
        Dafny.ISequence<Dafny.Rune> _2919_d = _2916___mcc_h5;
        Dafny.ISequence<Dafny.Rune> _2920_n = _2915___mcc_h4;
        {
          DAST._IType _source99 = _2918_t;
          if (_source99.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2921___mcc_h142 = _source99.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _2922___mcc_h143 = _source99.dtor_typeArgs;
            DAST._IResolvedType _2923___mcc_h144 = _source99.dtor_resolved;
            DAST._IType _2924_o = _2918_t;
            {
              RAST._IType _2925_genType;
              RAST._IType _out203;
              _out203 = (this).GenType(_2924_o, false, false);
              _2925_genType = _out203;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2920_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2919_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2925_genType);
            }
          } else if (_source99.is_Nullable) {
            DAST._IType _2926___mcc_h148 = _source99.dtor_Nullable_i_a0;
            DAST._IType _2927_o = _2918_t;
            {
              RAST._IType _2928_genType;
              RAST._IType _out204;
              _out204 = (this).GenType(_2927_o, false, false);
              _2928_genType = _out204;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2920_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2919_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2928_genType);
            }
          } else if (_source99.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2929___mcc_h150 = _source99.dtor_Tuple_i_a0;
            DAST._IType _2930_o = _2918_t;
            {
              RAST._IType _2931_genType;
              RAST._IType _out205;
              _out205 = (this).GenType(_2930_o, false, false);
              _2931_genType = _out205;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2920_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2919_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2931_genType);
            }
          } else if (_source99.is_Array) {
            DAST._IType _2932___mcc_h152 = _source99.dtor_element;
            BigInteger _2933___mcc_h153 = _source99.dtor_dims;
            DAST._IType _2934_o = _2918_t;
            {
              RAST._IType _2935_genType;
              RAST._IType _out206;
              _out206 = (this).GenType(_2934_o, false, false);
              _2935_genType = _out206;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2920_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2919_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2935_genType);
            }
          } else if (_source99.is_Seq) {
            DAST._IType _2936___mcc_h156 = _source99.dtor_element;
            DAST._IType _2937_o = _2918_t;
            {
              RAST._IType _2938_genType;
              RAST._IType _out207;
              _out207 = (this).GenType(_2937_o, false, false);
              _2938_genType = _out207;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2920_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2919_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2938_genType);
            }
          } else if (_source99.is_Set) {
            DAST._IType _2939___mcc_h158 = _source99.dtor_element;
            DAST._IType _2940_o = _2918_t;
            {
              RAST._IType _2941_genType;
              RAST._IType _out208;
              _out208 = (this).GenType(_2940_o, false, false);
              _2941_genType = _out208;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2920_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2919_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2941_genType);
            }
          } else if (_source99.is_Multiset) {
            DAST._IType _2942___mcc_h160 = _source99.dtor_element;
            DAST._IType _2943_o = _2918_t;
            {
              RAST._IType _2944_genType;
              RAST._IType _out209;
              _out209 = (this).GenType(_2943_o, false, false);
              _2944_genType = _out209;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2920_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2919_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2944_genType);
            }
          } else if (_source99.is_Map) {
            DAST._IType _2945___mcc_h162 = _source99.dtor_key;
            DAST._IType _2946___mcc_h163 = _source99.dtor_value;
            DAST._IType _2947_o = _2918_t;
            {
              RAST._IType _2948_genType;
              RAST._IType _out210;
              _out210 = (this).GenType(_2947_o, false, false);
              _2948_genType = _out210;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2920_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2919_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2948_genType);
            }
          } else if (_source99.is_SetBuilder) {
            DAST._IType _2949___mcc_h166 = _source99.dtor_element;
            DAST._IType _2950_o = _2918_t;
            {
              RAST._IType _2951_genType;
              RAST._IType _out211;
              _out211 = (this).GenType(_2950_o, false, false);
              _2951_genType = _out211;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2920_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2919_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2951_genType);
            }
          } else if (_source99.is_MapBuilder) {
            DAST._IType _2952___mcc_h168 = _source99.dtor_key;
            DAST._IType _2953___mcc_h169 = _source99.dtor_value;
            DAST._IType _2954_o = _2918_t;
            {
              RAST._IType _2955_genType;
              RAST._IType _out212;
              _out212 = (this).GenType(_2954_o, false, false);
              _2955_genType = _out212;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2920_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2919_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2955_genType);
            }
          } else if (_source99.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2956___mcc_h172 = _source99.dtor_args;
            DAST._IType _2957___mcc_h173 = _source99.dtor_result;
            DAST._IType _2958_o = _2918_t;
            {
              RAST._IType _2959_genType;
              RAST._IType _out213;
              _out213 = (this).GenType(_2958_o, false, false);
              _2959_genType = _out213;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2920_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2919_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2959_genType);
            }
          } else if (_source99.is_Primitive) {
            DAST._IPrimitive _2960___mcc_h176 = _source99.dtor_Primitive_i_a0;
            DAST._IPrimitive _source100 = _2960___mcc_h176;
            if (_source100.is_Int) {
              DAST._IType _2961_o = _2918_t;
              {
                RAST._IType _2962_genType;
                RAST._IType _out214;
                _out214 = (this).GenType(_2961_o, false, false);
                _2962_genType = _out214;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2920_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2919_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2962_genType);
              }
            } else if (_source100.is_Real) {
              {
                r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _2920_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _2919_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
              }
            } else if (_source100.is_String) {
              DAST._IType _2963_o = _2918_t;
              {
                RAST._IType _2964_genType;
                RAST._IType _out215;
                _out215 = (this).GenType(_2963_o, false, false);
                _2964_genType = _out215;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2920_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2919_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2964_genType);
              }
            } else if (_source100.is_Bool) {
              DAST._IType _2965_o = _2918_t;
              {
                RAST._IType _2966_genType;
                RAST._IType _out216;
                _out216 = (this).GenType(_2965_o, false, false);
                _2966_genType = _out216;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2920_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2919_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2966_genType);
              }
            } else {
              DAST._IType _2967_o = _2918_t;
              {
                RAST._IType _2968_genType;
                RAST._IType _out217;
                _out217 = (this).GenType(_2967_o, false, false);
                _2968_genType = _out217;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2920_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2919_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2968_genType);
              }
            }
          } else if (_source99.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2969___mcc_h178 = _source99.dtor_Passthrough_i_a0;
            DAST._IType _2970_o = _2918_t;
            {
              RAST._IType _2971_genType;
              RAST._IType _out218;
              _out218 = (this).GenType(_2970_o, false, false);
              _2971_genType = _out218;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2920_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2919_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2971_genType);
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2972___mcc_h180 = _source99.dtor_TypeArg_i_a0;
            DAST._IType _2973_o = _2918_t;
            {
              RAST._IType _2974_genType;
              RAST._IType _out219;
              _out219 = (this).GenType(_2973_o, false, false);
              _2974_genType = _out219;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2920_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2919_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2974_genType);
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
      } else if (_source96.is_StringLiteral) {
        Dafny.ISequence<Dafny.Rune> _2975___mcc_h7 = _source96.dtor_StringLiteral_i_a0;
        Dafny.ISequence<Dafny.Rune> _2976_l = _2975___mcc_h7;
        {
          r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_2976_l, false));
          RAST._IExpr _out222;
          DCOMP._IOwnership _out223;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out222, out _out223);
          r = _out222;
          resultingOwnership = _out223;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source96.is_CharLiteral) {
        Dafny.Rune _2977___mcc_h8 = _source96.dtor_CharLiteral_i_a0;
        Dafny.Rune _2978_c = _2977___mcc_h8;
        {
          r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_2978_c).Value)));
          r = RAST.Expr.create_TypeAscription(r, (this).DafnyCharUnderlying);
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
        DAST._IType _2979___mcc_h9 = _source96.dtor_Null_i_a0;
        DAST._IType _2980_tpe = _2979___mcc_h9;
        {
          RAST._IType _2981_tpeGen;
          RAST._IType _out226;
          _out226 = (this).GenType(_2980_tpe, false, false);
          _2981_tpeGen = _out226;
          r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None")), _2981_tpeGen);
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
      DAST._IBinOp _2982_op = _let_tmp_rhs52.dtor_op;
      DAST._IExpression _2983_lExpr = _let_tmp_rhs52.dtor_left;
      DAST._IExpression _2984_rExpr = _let_tmp_rhs52.dtor_right;
      DAST.Format._IBinaryOpFormat _2985_format = _let_tmp_rhs52.dtor_format2;
      bool _2986_becomesLeftCallsRight;
      _2986_becomesLeftCallsRight = ((System.Func<DAST._IBinOp, bool>)((_source101) => {
        if (_source101.is_Eq) {
          bool _2987___mcc_h0 = _source101.dtor_referential;
          bool _2988___mcc_h1 = _source101.dtor_nullable;
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
          return false;
        } else if (_source101.is_SeqProperPrefix) {
          return false;
        } else if (_source101.is_SeqPrefix) {
          return false;
        } else if (_source101.is_SetMerge) {
          return true;
        } else if (_source101.is_SetSubtraction) {
          return true;
        } else if (_source101.is_SetIntersection) {
          return true;
        } else if (_source101.is_Subset) {
          return false;
        } else if (_source101.is_ProperSubset) {
          return false;
        } else if (_source101.is_SetDisjoint) {
          return true;
        } else if (_source101.is_MapMerge) {
          return true;
        } else if (_source101.is_MapSubtraction) {
          return true;
        } else if (_source101.is_MultisetMerge) {
          return true;
        } else if (_source101.is_MultisetSubtraction) {
          return true;
        } else if (_source101.is_MultisetIntersection) {
          return true;
        } else if (_source101.is_Submultiset) {
          return false;
        } else if (_source101.is_ProperSubmultiset) {
          return false;
        } else if (_source101.is_MultisetDisjoint) {
          return true;
        } else if (_source101.is_Concat) {
          return true;
        } else {
          Dafny.ISequence<Dafny.Rune> _2989___mcc_h4 = _source101.dtor_Passthrough_i_a0;
          return false;
        }
      }))(_2982_op);
      bool _2990_becomesRightCallsLeft;
      _2990_becomesRightCallsLeft = ((System.Func<DAST._IBinOp, bool>)((_source102) => {
        if (_source102.is_Eq) {
          bool _2991___mcc_h6 = _source102.dtor_referential;
          bool _2992___mcc_h7 = _source102.dtor_nullable;
          return false;
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
          return true;
        } else if (_source102.is_SeqProperPrefix) {
          return false;
        } else if (_source102.is_SeqPrefix) {
          return false;
        } else if (_source102.is_SetMerge) {
          return false;
        } else if (_source102.is_SetSubtraction) {
          return false;
        } else if (_source102.is_SetIntersection) {
          return false;
        } else if (_source102.is_Subset) {
          return false;
        } else if (_source102.is_ProperSubset) {
          return false;
        } else if (_source102.is_SetDisjoint) {
          return false;
        } else if (_source102.is_MapMerge) {
          return false;
        } else if (_source102.is_MapSubtraction) {
          return false;
        } else if (_source102.is_MultisetMerge) {
          return false;
        } else if (_source102.is_MultisetSubtraction) {
          return false;
        } else if (_source102.is_MultisetIntersection) {
          return false;
        } else if (_source102.is_Submultiset) {
          return false;
        } else if (_source102.is_ProperSubmultiset) {
          return false;
        } else if (_source102.is_MultisetDisjoint) {
          return false;
        } else if (_source102.is_Concat) {
          return false;
        } else {
          Dafny.ISequence<Dafny.Rune> _2993___mcc_h10 = _source102.dtor_Passthrough_i_a0;
          return false;
        }
      }))(_2982_op);
      bool _2994_becomesCallLeftRight;
      _2994_becomesCallLeftRight = ((System.Func<DAST._IBinOp, bool>)((_source103) => {
        if (_source103.is_Eq) {
          bool _2995___mcc_h12 = _source103.dtor_referential;
          bool _2996___mcc_h13 = _source103.dtor_nullable;
          if ((_2995___mcc_h12) == (true)) {
            if ((_2996___mcc_h13) == (false)) {
              return true;
            } else {
              return false;
            }
          } else {
            return false;
          }
        } else if (_source103.is_Div) {
          return false;
        } else if (_source103.is_EuclidianDiv) {
          return false;
        } else if (_source103.is_Mod) {
          return false;
        } else if (_source103.is_EuclidianMod) {
          return false;
        } else if (_source103.is_Lt) {
          return false;
        } else if (_source103.is_LtChar) {
          return false;
        } else if (_source103.is_Plus) {
          return false;
        } else if (_source103.is_Minus) {
          return false;
        } else if (_source103.is_Times) {
          return false;
        } else if (_source103.is_BitwiseAnd) {
          return false;
        } else if (_source103.is_BitwiseOr) {
          return false;
        } else if (_source103.is_BitwiseXor) {
          return false;
        } else if (_source103.is_BitwiseShiftRight) {
          return false;
        } else if (_source103.is_BitwiseShiftLeft) {
          return false;
        } else if (_source103.is_And) {
          return false;
        } else if (_source103.is_Or) {
          return false;
        } else if (_source103.is_In) {
          return false;
        } else if (_source103.is_SeqProperPrefix) {
          return false;
        } else if (_source103.is_SeqPrefix) {
          return false;
        } else if (_source103.is_SetMerge) {
          return true;
        } else if (_source103.is_SetSubtraction) {
          return true;
        } else if (_source103.is_SetIntersection) {
          return true;
        } else if (_source103.is_Subset) {
          return false;
        } else if (_source103.is_ProperSubset) {
          return false;
        } else if (_source103.is_SetDisjoint) {
          return true;
        } else if (_source103.is_MapMerge) {
          return true;
        } else if (_source103.is_MapSubtraction) {
          return true;
        } else if (_source103.is_MultisetMerge) {
          return true;
        } else if (_source103.is_MultisetSubtraction) {
          return true;
        } else if (_source103.is_MultisetIntersection) {
          return true;
        } else if (_source103.is_Submultiset) {
          return false;
        } else if (_source103.is_ProperSubmultiset) {
          return false;
        } else if (_source103.is_MultisetDisjoint) {
          return true;
        } else if (_source103.is_Concat) {
          return true;
        } else {
          Dafny.ISequence<Dafny.Rune> _2997___mcc_h16 = _source103.dtor_Passthrough_i_a0;
          return false;
        }
      }))(_2982_op);
      DCOMP._IOwnership _2998_expectedLeftOwnership;
      _2998_expectedLeftOwnership = ((_2986_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_2990_becomesRightCallsLeft) || (_2994_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _2999_expectedRightOwnership;
      _2999_expectedRightOwnership = (((_2986_becomesLeftCallsRight) || (_2994_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_2990_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _3000_left;
      DCOMP._IOwnership _3001___v78;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3002_recIdentsL;
      RAST._IExpr _out229;
      DCOMP._IOwnership _out230;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out231;
      (this).GenExpr(_2983_lExpr, selfIdent, env, _2998_expectedLeftOwnership, out _out229, out _out230, out _out231);
      _3000_left = _out229;
      _3001___v78 = _out230;
      _3002_recIdentsL = _out231;
      RAST._IExpr _3003_right;
      DCOMP._IOwnership _3004___v79;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3005_recIdentsR;
      RAST._IExpr _out232;
      DCOMP._IOwnership _out233;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out234;
      (this).GenExpr(_2984_rExpr, selfIdent, env, _2999_expectedRightOwnership, out _out232, out _out233, out _out234);
      _3003_right = _out232;
      _3004___v79 = _out233;
      _3005_recIdentsR = _out234;
      DAST._IBinOp _source104 = _2982_op;
      if (_source104.is_Eq) {
        bool _3006___mcc_h18 = _source104.dtor_referential;
        bool _3007___mcc_h19 = _source104.dtor_nullable;
        {
          if ((DCOMP.COMP.OpTable).Contains(_2982_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2982_op), _3000_left, _3003_right, _2985_format);
          } else {
            DAST._IBinOp _source105 = _2982_op;
            if (_source105.is_Eq) {
              bool _3008___mcc_h24 = _source105.dtor_referential;
              bool _3009___mcc_h25 = _source105.dtor_nullable;
              bool _3010_nullable = _3009___mcc_h25;
              bool _3011_referential = _3008___mcc_h24;
              {
                if (_3011_referential) {
                  if (_3010_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3000_left, _3003_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source105.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else if (_source105.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3012___mcc_h26 = _source105.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3013_op = _3012___mcc_h26;
              {
                r = RAST.Expr.create_BinaryOp(_3013_op, _3000_left, _3003_right, _2985_format);
              }
            }
          }
        }
      } else if (_source104.is_Div) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2982_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2982_op), _3000_left, _3003_right, _2985_format);
          } else {
            DAST._IBinOp _source106 = _2982_op;
            if (_source106.is_Eq) {
              bool _3014___mcc_h27 = _source106.dtor_referential;
              bool _3015___mcc_h28 = _source106.dtor_nullable;
              bool _3016_nullable = _3015___mcc_h28;
              bool _3017_referential = _3014___mcc_h27;
              {
                if (_3017_referential) {
                  if (_3016_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3000_left, _3003_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source106.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else if (_source106.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3018___mcc_h29 = _source106.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3019_op = _3018___mcc_h29;
              {
                r = RAST.Expr.create_BinaryOp(_3019_op, _3000_left, _3003_right, _2985_format);
              }
            }
          }
        }
      } else if (_source104.is_EuclidianDiv) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2982_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2982_op), _3000_left, _3003_right, _2985_format);
          } else {
            DAST._IBinOp _source107 = _2982_op;
            if (_source107.is_Eq) {
              bool _3020___mcc_h30 = _source107.dtor_referential;
              bool _3021___mcc_h31 = _source107.dtor_nullable;
              bool _3022_nullable = _3021___mcc_h31;
              bool _3023_referential = _3020___mcc_h30;
              {
                if (_3023_referential) {
                  if (_3022_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3000_left, _3003_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source107.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else if (_source107.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3024___mcc_h32 = _source107.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3025_op = _3024___mcc_h32;
              {
                r = RAST.Expr.create_BinaryOp(_3025_op, _3000_left, _3003_right, _2985_format);
              }
            }
          }
        }
      } else if (_source104.is_Mod) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2982_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2982_op), _3000_left, _3003_right, _2985_format);
          } else {
            DAST._IBinOp _source108 = _2982_op;
            if (_source108.is_Eq) {
              bool _3026___mcc_h33 = _source108.dtor_referential;
              bool _3027___mcc_h34 = _source108.dtor_nullable;
              bool _3028_nullable = _3027___mcc_h34;
              bool _3029_referential = _3026___mcc_h33;
              {
                if (_3029_referential) {
                  if (_3028_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3000_left, _3003_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source108.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else if (_source108.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3030___mcc_h35 = _source108.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3031_op = _3030___mcc_h35;
              {
                r = RAST.Expr.create_BinaryOp(_3031_op, _3000_left, _3003_right, _2985_format);
              }
            }
          }
        }
      } else if (_source104.is_EuclidianMod) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2982_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2982_op), _3000_left, _3003_right, _2985_format);
          } else {
            DAST._IBinOp _source109 = _2982_op;
            if (_source109.is_Eq) {
              bool _3032___mcc_h36 = _source109.dtor_referential;
              bool _3033___mcc_h37 = _source109.dtor_nullable;
              bool _3034_nullable = _3033___mcc_h37;
              bool _3035_referential = _3032___mcc_h36;
              {
                if (_3035_referential) {
                  if (_3034_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3000_left, _3003_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source109.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else if (_source109.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3036___mcc_h38 = _source109.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3037_op = _3036___mcc_h38;
              {
                r = RAST.Expr.create_BinaryOp(_3037_op, _3000_left, _3003_right, _2985_format);
              }
            }
          }
        }
      } else if (_source104.is_Lt) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2982_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2982_op), _3000_left, _3003_right, _2985_format);
          } else {
            DAST._IBinOp _source110 = _2982_op;
            if (_source110.is_Eq) {
              bool _3038___mcc_h39 = _source110.dtor_referential;
              bool _3039___mcc_h40 = _source110.dtor_nullable;
              bool _3040_nullable = _3039___mcc_h40;
              bool _3041_referential = _3038___mcc_h39;
              {
                if (_3041_referential) {
                  if (_3040_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3000_left, _3003_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source110.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else if (_source110.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3042___mcc_h41 = _source110.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3043_op = _3042___mcc_h41;
              {
                r = RAST.Expr.create_BinaryOp(_3043_op, _3000_left, _3003_right, _2985_format);
              }
            }
          }
        }
      } else if (_source104.is_LtChar) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2982_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2982_op), _3000_left, _3003_right, _2985_format);
          } else {
            DAST._IBinOp _source111 = _2982_op;
            if (_source111.is_Eq) {
              bool _3044___mcc_h42 = _source111.dtor_referential;
              bool _3045___mcc_h43 = _source111.dtor_nullable;
              bool _3046_nullable = _3045___mcc_h43;
              bool _3047_referential = _3044___mcc_h42;
              {
                if (_3047_referential) {
                  if (_3046_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3000_left, _3003_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source111.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else if (_source111.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3048___mcc_h44 = _source111.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3049_op = _3048___mcc_h44;
              {
                r = RAST.Expr.create_BinaryOp(_3049_op, _3000_left, _3003_right, _2985_format);
              }
            }
          }
        }
      } else if (_source104.is_Plus) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2982_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2982_op), _3000_left, _3003_right, _2985_format);
          } else {
            DAST._IBinOp _source112 = _2982_op;
            if (_source112.is_Eq) {
              bool _3050___mcc_h45 = _source112.dtor_referential;
              bool _3051___mcc_h46 = _source112.dtor_nullable;
              bool _3052_nullable = _3051___mcc_h46;
              bool _3053_referential = _3050___mcc_h45;
              {
                if (_3053_referential) {
                  if (_3052_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3000_left, _3003_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source112.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else if (_source112.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3054___mcc_h47 = _source112.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3055_op = _3054___mcc_h47;
              {
                r = RAST.Expr.create_BinaryOp(_3055_op, _3000_left, _3003_right, _2985_format);
              }
            }
          }
        }
      } else if (_source104.is_Minus) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2982_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2982_op), _3000_left, _3003_right, _2985_format);
          } else {
            DAST._IBinOp _source113 = _2982_op;
            if (_source113.is_Eq) {
              bool _3056___mcc_h48 = _source113.dtor_referential;
              bool _3057___mcc_h49 = _source113.dtor_nullable;
              bool _3058_nullable = _3057___mcc_h49;
              bool _3059_referential = _3056___mcc_h48;
              {
                if (_3059_referential) {
                  if (_3058_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3000_left, _3003_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source113.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else if (_source113.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3060___mcc_h50 = _source113.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3061_op = _3060___mcc_h50;
              {
                r = RAST.Expr.create_BinaryOp(_3061_op, _3000_left, _3003_right, _2985_format);
              }
            }
          }
        }
      } else if (_source104.is_Times) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2982_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2982_op), _3000_left, _3003_right, _2985_format);
          } else {
            DAST._IBinOp _source114 = _2982_op;
            if (_source114.is_Eq) {
              bool _3062___mcc_h51 = _source114.dtor_referential;
              bool _3063___mcc_h52 = _source114.dtor_nullable;
              bool _3064_nullable = _3063___mcc_h52;
              bool _3065_referential = _3062___mcc_h51;
              {
                if (_3065_referential) {
                  if (_3064_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3000_left, _3003_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source114.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else if (_source114.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3066___mcc_h53 = _source114.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3067_op = _3066___mcc_h53;
              {
                r = RAST.Expr.create_BinaryOp(_3067_op, _3000_left, _3003_right, _2985_format);
              }
            }
          }
        }
      } else if (_source104.is_BitwiseAnd) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2982_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2982_op), _3000_left, _3003_right, _2985_format);
          } else {
            DAST._IBinOp _source115 = _2982_op;
            if (_source115.is_Eq) {
              bool _3068___mcc_h54 = _source115.dtor_referential;
              bool _3069___mcc_h55 = _source115.dtor_nullable;
              bool _3070_nullable = _3069___mcc_h55;
              bool _3071_referential = _3068___mcc_h54;
              {
                if (_3071_referential) {
                  if (_3070_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3000_left, _3003_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source115.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else if (_source115.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3072___mcc_h56 = _source115.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3073_op = _3072___mcc_h56;
              {
                r = RAST.Expr.create_BinaryOp(_3073_op, _3000_left, _3003_right, _2985_format);
              }
            }
          }
        }
      } else if (_source104.is_BitwiseOr) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2982_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2982_op), _3000_left, _3003_right, _2985_format);
          } else {
            DAST._IBinOp _source116 = _2982_op;
            if (_source116.is_Eq) {
              bool _3074___mcc_h57 = _source116.dtor_referential;
              bool _3075___mcc_h58 = _source116.dtor_nullable;
              bool _3076_nullable = _3075___mcc_h58;
              bool _3077_referential = _3074___mcc_h57;
              {
                if (_3077_referential) {
                  if (_3076_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3000_left, _3003_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source116.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else if (_source116.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3078___mcc_h59 = _source116.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3079_op = _3078___mcc_h59;
              {
                r = RAST.Expr.create_BinaryOp(_3079_op, _3000_left, _3003_right, _2985_format);
              }
            }
          }
        }
      } else if (_source104.is_BitwiseXor) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2982_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2982_op), _3000_left, _3003_right, _2985_format);
          } else {
            DAST._IBinOp _source117 = _2982_op;
            if (_source117.is_Eq) {
              bool _3080___mcc_h60 = _source117.dtor_referential;
              bool _3081___mcc_h61 = _source117.dtor_nullable;
              bool _3082_nullable = _3081___mcc_h61;
              bool _3083_referential = _3080___mcc_h60;
              {
                if (_3083_referential) {
                  if (_3082_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3000_left, _3003_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source117.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else if (_source117.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3084___mcc_h62 = _source117.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3085_op = _3084___mcc_h62;
              {
                r = RAST.Expr.create_BinaryOp(_3085_op, _3000_left, _3003_right, _2985_format);
              }
            }
          }
        }
      } else if (_source104.is_BitwiseShiftRight) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2982_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2982_op), _3000_left, _3003_right, _2985_format);
          } else {
            DAST._IBinOp _source118 = _2982_op;
            if (_source118.is_Eq) {
              bool _3086___mcc_h63 = _source118.dtor_referential;
              bool _3087___mcc_h64 = _source118.dtor_nullable;
              bool _3088_nullable = _3087___mcc_h64;
              bool _3089_referential = _3086___mcc_h63;
              {
                if (_3089_referential) {
                  if (_3088_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3000_left, _3003_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source118.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else if (_source118.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3090___mcc_h65 = _source118.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3091_op = _3090___mcc_h65;
              {
                r = RAST.Expr.create_BinaryOp(_3091_op, _3000_left, _3003_right, _2985_format);
              }
            }
          }
        }
      } else if (_source104.is_BitwiseShiftLeft) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2982_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2982_op), _3000_left, _3003_right, _2985_format);
          } else {
            DAST._IBinOp _source119 = _2982_op;
            if (_source119.is_Eq) {
              bool _3092___mcc_h66 = _source119.dtor_referential;
              bool _3093___mcc_h67 = _source119.dtor_nullable;
              bool _3094_nullable = _3093___mcc_h67;
              bool _3095_referential = _3092___mcc_h66;
              {
                if (_3095_referential) {
                  if (_3094_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3000_left, _3003_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source119.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else if (_source119.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3096___mcc_h68 = _source119.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3097_op = _3096___mcc_h68;
              {
                r = RAST.Expr.create_BinaryOp(_3097_op, _3000_left, _3003_right, _2985_format);
              }
            }
          }
        }
      } else if (_source104.is_And) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2982_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2982_op), _3000_left, _3003_right, _2985_format);
          } else {
            DAST._IBinOp _source120 = _2982_op;
            if (_source120.is_Eq) {
              bool _3098___mcc_h69 = _source120.dtor_referential;
              bool _3099___mcc_h70 = _source120.dtor_nullable;
              bool _3100_nullable = _3099___mcc_h70;
              bool _3101_referential = _3098___mcc_h69;
              {
                if (_3101_referential) {
                  if (_3100_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3000_left, _3003_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source120.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else if (_source120.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3102___mcc_h71 = _source120.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3103_op = _3102___mcc_h71;
              {
                r = RAST.Expr.create_BinaryOp(_3103_op, _3000_left, _3003_right, _2985_format);
              }
            }
          }
        }
      } else if (_source104.is_Or) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2982_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2982_op), _3000_left, _3003_right, _2985_format);
          } else {
            DAST._IBinOp _source121 = _2982_op;
            if (_source121.is_Eq) {
              bool _3104___mcc_h72 = _source121.dtor_referential;
              bool _3105___mcc_h73 = _source121.dtor_nullable;
              bool _3106_nullable = _3105___mcc_h73;
              bool _3107_referential = _3104___mcc_h72;
              {
                if (_3107_referential) {
                  if (_3106_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3000_left, _3003_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source121.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else if (_source121.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3108___mcc_h74 = _source121.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3109_op = _3108___mcc_h74;
              {
                r = RAST.Expr.create_BinaryOp(_3109_op, _3000_left, _3003_right, _2985_format);
              }
            }
          }
        }
      } else if (_source104.is_In) {
        {
          r = ((_3003_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_3000_left);
        }
      } else if (_source104.is_SeqProperPrefix) {
        r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _3000_left, _3003_right, _2985_format);
      } else if (_source104.is_SeqPrefix) {
        r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _3000_left, _3003_right, _2985_format);
      } else if (_source104.is_SetMerge) {
        {
          r = ((_3000_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_3003_right);
        }
      } else if (_source104.is_SetSubtraction) {
        {
          r = ((_3000_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_3003_right);
        }
      } else if (_source104.is_SetIntersection) {
        {
          r = ((_3000_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_3003_right);
        }
      } else if (_source104.is_Subset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _3000_left, _3003_right, _2985_format);
        }
      } else if (_source104.is_ProperSubset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _3000_left, _3003_right, _2985_format);
        }
      } else if (_source104.is_SetDisjoint) {
        {
          r = ((_3000_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_3003_right);
        }
      } else if (_source104.is_MapMerge) {
        {
          r = ((_3000_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_3003_right);
        }
      } else if (_source104.is_MapSubtraction) {
        {
          r = ((_3000_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_3003_right);
        }
      } else if (_source104.is_MultisetMerge) {
        {
          r = ((_3000_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_3003_right);
        }
      } else if (_source104.is_MultisetSubtraction) {
        {
          r = ((_3000_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_3003_right);
        }
      } else if (_source104.is_MultisetIntersection) {
        {
          r = ((_3000_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_3003_right);
        }
      } else if (_source104.is_Submultiset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _3000_left, _3003_right, _2985_format);
        }
      } else if (_source104.is_ProperSubmultiset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _3000_left, _3003_right, _2985_format);
        }
      } else if (_source104.is_MultisetDisjoint) {
        {
          r = ((_3000_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_3003_right);
        }
      } else if (_source104.is_Concat) {
        {
          r = ((_3000_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_3003_right);
        }
      } else {
        Dafny.ISequence<Dafny.Rune> _3110___mcc_h22 = _source104.dtor_Passthrough_i_a0;
        {
          if ((DCOMP.COMP.OpTable).Contains(_2982_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2982_op), _3000_left, _3003_right, _2985_format);
          } else {
            DAST._IBinOp _source122 = _2982_op;
            if (_source122.is_Eq) {
              bool _3111___mcc_h75 = _source122.dtor_referential;
              bool _3112___mcc_h76 = _source122.dtor_nullable;
              bool _3113_nullable = _3112___mcc_h76;
              bool _3114_referential = _3111___mcc_h75;
              {
                if (_3114_referential) {
                  if (_3113_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3000_left, _3003_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source122.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else if (_source122.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3000_left, _3003_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3115___mcc_h77 = _source122.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3116_op = _3115___mcc_h77;
              {
                r = RAST.Expr.create_BinaryOp(_3116_op, _3000_left, _3003_right, _2985_format);
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
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_3002_recIdentsL, _3005_recIdentsR);
      return ;
    }
    public void GenExprConvertFromNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs53 = e;
      DAST._IExpression _3117_expr = _let_tmp_rhs53.dtor_value;
      DAST._IType _3118_fromTpe = _let_tmp_rhs53.dtor_from;
      DAST._IType _3119_toTpe = _let_tmp_rhs53.dtor_typ;
      RAST._IExpr _3120_recursiveGen;
      DCOMP._IOwnership _3121_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3122_recIdents;
      RAST._IExpr _out237;
      DCOMP._IOwnership _out238;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out239;
      (this).GenExpr(_3117_expr, selfIdent, env, expectedOwnership, out _out237, out _out238, out _out239);
      _3120_recursiveGen = _out237;
      _3121_recOwned = _out238;
      _3122_recIdents = _out239;
      r = _3120_recursiveGen;
      if (object.Equals(_3121_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      RAST._IExpr _out240;
      DCOMP._IOwnership _out241;
      DCOMP.COMP.FromOwnership(r, _3121_recOwned, expectedOwnership, out _out240, out _out241);
      r = _out240;
      resultingOwnership = _out241;
      readIdents = _3122_recIdents;
    }
    public void GenExprConvertToNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IExpression _3123_expr = _let_tmp_rhs54.dtor_value;
      DAST._IType _3124_fromTpe = _let_tmp_rhs54.dtor_from;
      DAST._IType _3125_toTpe = _let_tmp_rhs54.dtor_typ;
      RAST._IExpr _3126_recursiveGen;
      DCOMP._IOwnership _3127_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3128_recIdents;
      RAST._IExpr _out242;
      DCOMP._IOwnership _out243;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out244;
      (this).GenExpr(_3123_expr, selfIdent, env, expectedOwnership, out _out242, out _out243, out _out244);
      _3126_recursiveGen = _out242;
      _3127_recOwned = _out243;
      _3128_recIdents = _out244;
      r = _3126_recursiveGen;
      if (object.Equals(_3127_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
      RAST._IExpr _out245;
      DCOMP._IOwnership _out246;
      DCOMP.COMP.FromOwnership(r, _3127_recOwned, expectedOwnership, out _out245, out _out246);
      r = _out245;
      resultingOwnership = _out246;
      readIdents = _3128_recIdents;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _3129_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _3130_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _3131_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _3131_toTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3132___v81 = _let_tmp_rhs56.dtor_Path_i_a0;
      Dafny.ISequence<DAST._IType> _3133___v82 = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      DAST._IType _3134_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _3135_range = _let_tmp_rhs57.dtor_range;
      bool _3136_erase = _let_tmp_rhs57.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _3137_attributes = _let_tmp_rhs57.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _3138_nativeToType;
      _3138_nativeToType = DCOMP.COMP.NewtypeToRustType(_3134_b, _3135_range);
      if (object.Equals(_3130_fromTpe, _3134_b)) {
        RAST._IExpr _3139_recursiveGen;
        DCOMP._IOwnership _3140_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3141_recIdents;
        RAST._IExpr _out247;
        DCOMP._IOwnership _out248;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out249;
        (this).GenExpr(_3129_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out247, out _out248, out _out249);
        _3139_recursiveGen = _out247;
        _3140_recOwned = _out248;
        _3141_recIdents = _out249;
        readIdents = _3141_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source123 = _3138_nativeToType;
        if (_source123.is_None) {
          if (_3136_erase) {
            r = _3139_recursiveGen;
          } else {
            RAST._IType _3142_rhsType;
            RAST._IType _out250;
            _out250 = (this).GenType(_3131_toTpe, true, false);
            _3142_rhsType = _out250;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_3142_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_3139_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out251;
          DCOMP._IOwnership _out252;
          DCOMP.COMP.FromOwnership(r, _3140_recOwned, expectedOwnership, out _out251, out _out252);
          r = _out251;
          resultingOwnership = _out252;
        } else {
          RAST._IType _3143___mcc_h0 = _source123.dtor_value;
          RAST._IType _3144_v = _3143___mcc_h0;
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3139_recursiveGen, RAST.Expr.create_ExprFromType(_3144_v)));
          RAST._IExpr _out253;
          DCOMP._IOwnership _out254;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out253, out _out254);
          r = _out253;
          resultingOwnership = _out254;
        }
      } else {
        if ((_3138_nativeToType).is_Some) {
          DAST._IType _source124 = _3130_fromTpe;
          if (_source124.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3145___mcc_h1 = _source124.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3146___mcc_h2 = _source124.dtor_typeArgs;
            DAST._IResolvedType _3147___mcc_h3 = _source124.dtor_resolved;
            DAST._IResolvedType _source125 = _3147___mcc_h3;
            if (_source125.is_Datatype) {
              DAST._IDatatypeType _3148___mcc_h7 = _source125.dtor_datatypeType;
            } else if (_source125.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3149___mcc_h9 = _source125.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3150___mcc_h10 = _source125.dtor_attributes;
            } else {
              DAST._IType _3151___mcc_h13 = _source125.dtor_baseType;
              DAST._INewtypeRange _3152___mcc_h14 = _source125.dtor_range;
              bool _3153___mcc_h15 = _source125.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3154___mcc_h16 = _source125.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3155_attributes0 = _3154___mcc_h16;
              bool _3156_erase0 = _3153___mcc_h15;
              DAST._INewtypeRange _3157_range0 = _3152___mcc_h14;
              DAST._IType _3158_b0 = _3151___mcc_h13;
              {
                Std.Wrappers._IOption<RAST._IType> _3159_nativeFromType;
                _3159_nativeFromType = DCOMP.COMP.NewtypeToRustType(_3158_b0, _3157_range0);
                if ((_3159_nativeFromType).is_Some) {
                  RAST._IExpr _3160_recursiveGen;
                  DCOMP._IOwnership _3161_recOwned;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3162_recIdents;
                  RAST._IExpr _out255;
                  DCOMP._IOwnership _out256;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out257;
                  (this).GenExpr(_3129_expr, selfIdent, env, expectedOwnership, out _out255, out _out256, out _out257);
                  _3160_recursiveGen = _out255;
                  _3161_recOwned = _out256;
                  _3162_recIdents = _out257;
                  RAST._IExpr _out258;
                  DCOMP._IOwnership _out259;
                  DCOMP.COMP.FromOwnership(RAST.Expr.create_TypeAscription(_3160_recursiveGen, (_3138_nativeToType).dtor_value), _3161_recOwned, expectedOwnership, out _out258, out _out259);
                  r = _out258;
                  resultingOwnership = _out259;
                  readIdents = _3162_recIdents;
                  return ;
                }
              }
            }
          } else if (_source124.is_Nullable) {
            DAST._IType _3163___mcc_h21 = _source124.dtor_Nullable_i_a0;
          } else if (_source124.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3164___mcc_h23 = _source124.dtor_Tuple_i_a0;
          } else if (_source124.is_Array) {
            DAST._IType _3165___mcc_h25 = _source124.dtor_element;
            BigInteger _3166___mcc_h26 = _source124.dtor_dims;
          } else if (_source124.is_Seq) {
            DAST._IType _3167___mcc_h29 = _source124.dtor_element;
          } else if (_source124.is_Set) {
            DAST._IType _3168___mcc_h31 = _source124.dtor_element;
          } else if (_source124.is_Multiset) {
            DAST._IType _3169___mcc_h33 = _source124.dtor_element;
          } else if (_source124.is_Map) {
            DAST._IType _3170___mcc_h35 = _source124.dtor_key;
            DAST._IType _3171___mcc_h36 = _source124.dtor_value;
          } else if (_source124.is_SetBuilder) {
            DAST._IType _3172___mcc_h39 = _source124.dtor_element;
          } else if (_source124.is_MapBuilder) {
            DAST._IType _3173___mcc_h41 = _source124.dtor_key;
            DAST._IType _3174___mcc_h42 = _source124.dtor_value;
          } else if (_source124.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3175___mcc_h45 = _source124.dtor_args;
            DAST._IType _3176___mcc_h46 = _source124.dtor_result;
          } else if (_source124.is_Primitive) {
            DAST._IPrimitive _3177___mcc_h49 = _source124.dtor_Primitive_i_a0;
          } else if (_source124.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3178___mcc_h51 = _source124.dtor_Passthrough_i_a0;
          } else {
            Dafny.ISequence<Dafny.Rune> _3179___mcc_h53 = _source124.dtor_TypeArg_i_a0;
          }
          if (object.Equals(_3130_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _3180_recursiveGen;
            DCOMP._IOwnership _3181_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3182_recIdents;
            RAST._IExpr _out260;
            DCOMP._IOwnership _out261;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out262;
            (this).GenExpr(_3129_expr, selfIdent, env, expectedOwnership, out _out260, out _out261, out _out262);
            _3180_recursiveGen = _out260;
            _3181_recOwned = _out261;
            _3182_recIdents = _out262;
            RAST._IExpr _out263;
            DCOMP._IOwnership _out264;
            DCOMP.COMP.FromOwnership(RAST.Expr.create_TypeAscription((_3180_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_3138_nativeToType).dtor_value), _3181_recOwned, expectedOwnership, out _out263, out _out264);
            r = _out263;
            resultingOwnership = _out264;
            readIdents = _3182_recIdents;
            return ;
          }
        }
        RAST._IExpr _out265;
        DCOMP._IOwnership _out266;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out267;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_3129_expr, _3130_fromTpe, _3134_b), _3134_b, _3131_toTpe), selfIdent, env, expectedOwnership, out _out265, out _out266, out _out267);
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
      DAST._IExpression _3183_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _3184_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _3185_toTpe = _let_tmp_rhs58.dtor_typ;
      DAST._IType _let_tmp_rhs59 = _3184_fromTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3186___v86 = _let_tmp_rhs59.dtor_Path_i_a0;
      Dafny.ISequence<DAST._IType> _3187___v87 = _let_tmp_rhs59.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs60 = _let_tmp_rhs59.dtor_resolved;
      DAST._IType _3188_b = _let_tmp_rhs60.dtor_baseType;
      DAST._INewtypeRange _3189_range = _let_tmp_rhs60.dtor_range;
      bool _3190_erase = _let_tmp_rhs60.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _3191_attributes = _let_tmp_rhs60.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _3192_nativeFromType;
      _3192_nativeFromType = DCOMP.COMP.NewtypeToRustType(_3188_b, _3189_range);
      if (object.Equals(_3188_b, _3185_toTpe)) {
        RAST._IExpr _3193_recursiveGen;
        DCOMP._IOwnership _3194_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3195_recIdents;
        RAST._IExpr _out268;
        DCOMP._IOwnership _out269;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out270;
        (this).GenExpr(_3183_expr, selfIdent, env, expectedOwnership, out _out268, out _out269, out _out270);
        _3193_recursiveGen = _out268;
        _3194_recOwned = _out269;
        _3195_recIdents = _out270;
        readIdents = _3195_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source126 = _3192_nativeFromType;
        if (_source126.is_None) {
          if (_3190_erase) {
            r = _3193_recursiveGen;
          } else {
            r = (_3193_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out271;
          DCOMP._IOwnership _out272;
          DCOMP.COMP.FromOwnership(r, _3194_recOwned, expectedOwnership, out _out271, out _out272);
          r = _out271;
          resultingOwnership = _out272;
        } else {
          RAST._IType _3196___mcc_h0 = _source126.dtor_value;
          RAST._IType _3197_v = _3196___mcc_h0;
          RAST._IType _3198_toTpeRust;
          RAST._IType _out273;
          _out273 = (this).GenType(_3185_toTpe, false, false);
          _3198_toTpeRust = _out273;
          r = (((_3193_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_3198_toTpeRust))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out274;
          DCOMP._IOwnership _out275;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out274, out _out275);
          r = _out274;
          resultingOwnership = _out275;
        }
      } else {
        if ((_3192_nativeFromType).is_Some) {
          if (object.Equals(_3185_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _3199_recursiveGen;
            DCOMP._IOwnership _3200_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3201_recIdents;
            RAST._IExpr _out276;
            DCOMP._IOwnership _out277;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out278;
            (this).GenExpr(_3183_expr, selfIdent, env, expectedOwnership, out _out276, out _out277, out _out278);
            _3199_recursiveGen = _out276;
            _3200_recOwned = _out277;
            _3201_recIdents = _out278;
            RAST._IExpr _out279;
            DCOMP._IOwnership _out280;
            DCOMP.COMP.FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_3199_recursiveGen, (this).DafnyCharUnderlying)), _3200_recOwned, expectedOwnership, out _out279, out _out280);
            r = _out279;
            resultingOwnership = _out280;
            readIdents = _3201_recIdents;
            return ;
          }
        }
        RAST._IExpr _out281;
        DCOMP._IOwnership _out282;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out283;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_3183_expr, _3184_fromTpe, _3188_b), _3188_b, _3185_toTpe), selfIdent, env, expectedOwnership, out _out281, out _out282, out _out283);
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
      DAST._IExpression _3202_expr = _let_tmp_rhs61.dtor_value;
      DAST._IType _3203_fromTpe = _let_tmp_rhs61.dtor_from;
      DAST._IType _3204_toTpe = _let_tmp_rhs61.dtor_typ;
      RAST._IType _3205_fromTpeGen;
      RAST._IType _out284;
      _out284 = (this).GenType(_3203_fromTpe, true, false);
      _3205_fromTpeGen = _out284;
      RAST._IType _3206_toTpeGen;
      RAST._IType _out285;
      _out285 = (this).GenType(_3204_toTpe, true, false);
      _3206_toTpeGen = _out285;
      RAST._IExpr _3207_recursiveGen;
      DCOMP._IOwnership _3208_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3209_recIdents;
      RAST._IExpr _out286;
      DCOMP._IOwnership _out287;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out288;
      (this).GenExpr(_3202_expr, selfIdent, env, expectedOwnership, out _out286, out _out287, out _out288);
      _3207_recursiveGen = _out286;
      _3208_recOwned = _out287;
      _3209_recIdents = _out288;
      Dafny.ISequence<Dafny.Rune> _3210_msg;
      _3210_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_3205_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_3206_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_3210_msg);
      r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_3207_recursiveGen)._ToString(DCOMP.__default.IND), _3210_msg));
      RAST._IExpr _out289;
      DCOMP._IOwnership _out290;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out289, out _out290);
      r = _out289;
      resultingOwnership = _out290;
      readIdents = _3209_recIdents;
    }
    public void GenExprConvert(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs62 = e;
      DAST._IExpression _3211_expr = _let_tmp_rhs62.dtor_value;
      DAST._IType _3212_fromTpe = _let_tmp_rhs62.dtor_from;
      DAST._IType _3213_toTpe = _let_tmp_rhs62.dtor_typ;
      if (object.Equals(_3212_fromTpe, _3213_toTpe)) {
        RAST._IExpr _3214_recursiveGen;
        DCOMP._IOwnership _3215_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3216_recIdents;
        RAST._IExpr _out291;
        DCOMP._IOwnership _out292;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out293;
        (this).GenExpr(_3211_expr, selfIdent, env, expectedOwnership, out _out291, out _out292, out _out293);
        _3214_recursiveGen = _out291;
        _3215_recOwned = _out292;
        _3216_recIdents = _out293;
        r = _3214_recursiveGen;
        RAST._IExpr _out294;
        DCOMP._IOwnership _out295;
        DCOMP.COMP.FromOwnership(r, _3215_recOwned, expectedOwnership, out _out294, out _out295);
        r = _out294;
        resultingOwnership = _out295;
        readIdents = _3216_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source127 = _System.Tuple2<DAST._IType, DAST._IType>.create(_3212_fromTpe, _3213_toTpe);
        DAST._IType _3217___mcc_h0 = _source127.dtor__0;
        DAST._IType _3218___mcc_h1 = _source127.dtor__1;
        DAST._IType _source128 = _3217___mcc_h0;
        if (_source128.is_Path) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3219___mcc_h4 = _source128.dtor_Path_i_a0;
          Dafny.ISequence<DAST._IType> _3220___mcc_h5 = _source128.dtor_typeArgs;
          DAST._IResolvedType _3221___mcc_h6 = _source128.dtor_resolved;
          DAST._IResolvedType _source129 = _3221___mcc_h6;
          if (_source129.is_Datatype) {
            DAST._IDatatypeType _3222___mcc_h16 = _source129.dtor_datatypeType;
            DAST._IType _source130 = _3218___mcc_h1;
            if (_source130.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3223___mcc_h20 = _source130.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3224___mcc_h21 = _source130.dtor_typeArgs;
              DAST._IResolvedType _3225___mcc_h22 = _source130.dtor_resolved;
              DAST._IResolvedType _source131 = _3225___mcc_h22;
              if (_source131.is_Datatype) {
                DAST._IDatatypeType _3226___mcc_h26 = _source131.dtor_datatypeType;
                {
                  RAST._IExpr _out296;
                  DCOMP._IOwnership _out297;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out298;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out296, out _out297, out _out298);
                  r = _out296;
                  resultingOwnership = _out297;
                  readIdents = _out298;
                }
              } else if (_source131.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3227___mcc_h28 = _source131.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3228___mcc_h29 = _source131.dtor_attributes;
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
                DAST._IType _3229___mcc_h32 = _source131.dtor_baseType;
                DAST._INewtypeRange _3230___mcc_h33 = _source131.dtor_range;
                bool _3231___mcc_h34 = _source131.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3232___mcc_h35 = _source131.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3233_attributes = _3232___mcc_h35;
                bool _3234_erase = _3231___mcc_h34;
                DAST._INewtypeRange _3235_range = _3230___mcc_h33;
                DAST._IType _3236_b = _3229___mcc_h32;
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
            } else if (_source130.is_Nullable) {
              DAST._IType _3237___mcc_h40 = _source130.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out305;
                DCOMP._IOwnership _out306;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out307;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out305, out _out306, out _out307);
                r = _out305;
                resultingOwnership = _out306;
                readIdents = _out307;
              }
            } else if (_source130.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3238___mcc_h42 = _source130.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out308;
                DCOMP._IOwnership _out309;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out310;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out308, out _out309, out _out310);
                r = _out308;
                resultingOwnership = _out309;
                readIdents = _out310;
              }
            } else if (_source130.is_Array) {
              DAST._IType _3239___mcc_h44 = _source130.dtor_element;
              BigInteger _3240___mcc_h45 = _source130.dtor_dims;
              {
                RAST._IExpr _out311;
                DCOMP._IOwnership _out312;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out313;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out311, out _out312, out _out313);
                r = _out311;
                resultingOwnership = _out312;
                readIdents = _out313;
              }
            } else if (_source130.is_Seq) {
              DAST._IType _3241___mcc_h48 = _source130.dtor_element;
              {
                RAST._IExpr _out314;
                DCOMP._IOwnership _out315;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out316;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out314, out _out315, out _out316);
                r = _out314;
                resultingOwnership = _out315;
                readIdents = _out316;
              }
            } else if (_source130.is_Set) {
              DAST._IType _3242___mcc_h50 = _source130.dtor_element;
              {
                RAST._IExpr _out317;
                DCOMP._IOwnership _out318;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out319;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out317, out _out318, out _out319);
                r = _out317;
                resultingOwnership = _out318;
                readIdents = _out319;
              }
            } else if (_source130.is_Multiset) {
              DAST._IType _3243___mcc_h52 = _source130.dtor_element;
              {
                RAST._IExpr _out320;
                DCOMP._IOwnership _out321;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out322;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out320, out _out321, out _out322);
                r = _out320;
                resultingOwnership = _out321;
                readIdents = _out322;
              }
            } else if (_source130.is_Map) {
              DAST._IType _3244___mcc_h54 = _source130.dtor_key;
              DAST._IType _3245___mcc_h55 = _source130.dtor_value;
              {
                RAST._IExpr _out323;
                DCOMP._IOwnership _out324;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out325;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out323, out _out324, out _out325);
                r = _out323;
                resultingOwnership = _out324;
                readIdents = _out325;
              }
            } else if (_source130.is_SetBuilder) {
              DAST._IType _3246___mcc_h58 = _source130.dtor_element;
              {
                RAST._IExpr _out326;
                DCOMP._IOwnership _out327;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out328;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out326, out _out327, out _out328);
                r = _out326;
                resultingOwnership = _out327;
                readIdents = _out328;
              }
            } else if (_source130.is_MapBuilder) {
              DAST._IType _3247___mcc_h60 = _source130.dtor_key;
              DAST._IType _3248___mcc_h61 = _source130.dtor_value;
              {
                RAST._IExpr _out329;
                DCOMP._IOwnership _out330;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out329, out _out330, out _out331);
                r = _out329;
                resultingOwnership = _out330;
                readIdents = _out331;
              }
            } else if (_source130.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3249___mcc_h64 = _source130.dtor_args;
              DAST._IType _3250___mcc_h65 = _source130.dtor_result;
              {
                RAST._IExpr _out332;
                DCOMP._IOwnership _out333;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out334;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out332, out _out333, out _out334);
                r = _out332;
                resultingOwnership = _out333;
                readIdents = _out334;
              }
            } else if (_source130.is_Primitive) {
              DAST._IPrimitive _3251___mcc_h68 = _source130.dtor_Primitive_i_a0;
              {
                RAST._IExpr _out335;
                DCOMP._IOwnership _out336;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out337;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out335, out _out336, out _out337);
                r = _out335;
                resultingOwnership = _out336;
                readIdents = _out337;
              }
            } else if (_source130.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3252___mcc_h70 = _source130.dtor_Passthrough_i_a0;
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
              Dafny.ISequence<Dafny.Rune> _3253___mcc_h72 = _source130.dtor_TypeArg_i_a0;
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
          } else if (_source129.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3254___mcc_h74 = _source129.dtor_path;
            Dafny.ISequence<DAST._IAttribute> _3255___mcc_h75 = _source129.dtor_attributes;
            DAST._IType _source132 = _3218___mcc_h1;
            if (_source132.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3256___mcc_h82 = _source132.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3257___mcc_h83 = _source132.dtor_typeArgs;
              DAST._IResolvedType _3258___mcc_h84 = _source132.dtor_resolved;
              DAST._IResolvedType _source133 = _3258___mcc_h84;
              if (_source133.is_Datatype) {
                DAST._IDatatypeType _3259___mcc_h88 = _source133.dtor_datatypeType;
                {
                  RAST._IExpr _out344;
                  DCOMP._IOwnership _out345;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out346;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out344, out _out345, out _out346);
                  r = _out344;
                  resultingOwnership = _out345;
                  readIdents = _out346;
                }
              } else if (_source133.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3260___mcc_h90 = _source133.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3261___mcc_h91 = _source133.dtor_attributes;
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
                DAST._IType _3262___mcc_h94 = _source133.dtor_baseType;
                DAST._INewtypeRange _3263___mcc_h95 = _source133.dtor_range;
                bool _3264___mcc_h96 = _source133.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3265___mcc_h97 = _source133.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3266_attributes = _3265___mcc_h97;
                bool _3267_erase = _3264___mcc_h96;
                DAST._INewtypeRange _3268_range = _3263___mcc_h95;
                DAST._IType _3269_b = _3262___mcc_h94;
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
            } else if (_source132.is_Nullable) {
              DAST._IType _3270___mcc_h102 = _source132.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out353;
                DCOMP._IOwnership _out354;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out355;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out353, out _out354, out _out355);
                r = _out353;
                resultingOwnership = _out354;
                readIdents = _out355;
              }
            } else if (_source132.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3271___mcc_h104 = _source132.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out356;
                DCOMP._IOwnership _out357;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out358;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out356, out _out357, out _out358);
                r = _out356;
                resultingOwnership = _out357;
                readIdents = _out358;
              }
            } else if (_source132.is_Array) {
              DAST._IType _3272___mcc_h106 = _source132.dtor_element;
              BigInteger _3273___mcc_h107 = _source132.dtor_dims;
              {
                RAST._IExpr _out359;
                DCOMP._IOwnership _out360;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out361;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out359, out _out360, out _out361);
                r = _out359;
                resultingOwnership = _out360;
                readIdents = _out361;
              }
            } else if (_source132.is_Seq) {
              DAST._IType _3274___mcc_h110 = _source132.dtor_element;
              {
                RAST._IExpr _out362;
                DCOMP._IOwnership _out363;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out364;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out362, out _out363, out _out364);
                r = _out362;
                resultingOwnership = _out363;
                readIdents = _out364;
              }
            } else if (_source132.is_Set) {
              DAST._IType _3275___mcc_h112 = _source132.dtor_element;
              {
                RAST._IExpr _out365;
                DCOMP._IOwnership _out366;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out367;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out365, out _out366, out _out367);
                r = _out365;
                resultingOwnership = _out366;
                readIdents = _out367;
              }
            } else if (_source132.is_Multiset) {
              DAST._IType _3276___mcc_h114 = _source132.dtor_element;
              {
                RAST._IExpr _out368;
                DCOMP._IOwnership _out369;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out370;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out368, out _out369, out _out370);
                r = _out368;
                resultingOwnership = _out369;
                readIdents = _out370;
              }
            } else if (_source132.is_Map) {
              DAST._IType _3277___mcc_h116 = _source132.dtor_key;
              DAST._IType _3278___mcc_h117 = _source132.dtor_value;
              {
                RAST._IExpr _out371;
                DCOMP._IOwnership _out372;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out373;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out371, out _out372, out _out373);
                r = _out371;
                resultingOwnership = _out372;
                readIdents = _out373;
              }
            } else if (_source132.is_SetBuilder) {
              DAST._IType _3279___mcc_h120 = _source132.dtor_element;
              {
                RAST._IExpr _out374;
                DCOMP._IOwnership _out375;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out376;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out374, out _out375, out _out376);
                r = _out374;
                resultingOwnership = _out375;
                readIdents = _out376;
              }
            } else if (_source132.is_MapBuilder) {
              DAST._IType _3280___mcc_h122 = _source132.dtor_key;
              DAST._IType _3281___mcc_h123 = _source132.dtor_value;
              {
                RAST._IExpr _out377;
                DCOMP._IOwnership _out378;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out379;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out377, out _out378, out _out379);
                r = _out377;
                resultingOwnership = _out378;
                readIdents = _out379;
              }
            } else if (_source132.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3282___mcc_h126 = _source132.dtor_args;
              DAST._IType _3283___mcc_h127 = _source132.dtor_result;
              {
                RAST._IExpr _out380;
                DCOMP._IOwnership _out381;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out382;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out380, out _out381, out _out382);
                r = _out380;
                resultingOwnership = _out381;
                readIdents = _out382;
              }
            } else if (_source132.is_Primitive) {
              DAST._IPrimitive _3284___mcc_h130 = _source132.dtor_Primitive_i_a0;
              {
                RAST._IExpr _out383;
                DCOMP._IOwnership _out384;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out385;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out383, out _out384, out _out385);
                r = _out383;
                resultingOwnership = _out384;
                readIdents = _out385;
              }
            } else if (_source132.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3285___mcc_h132 = _source132.dtor_Passthrough_i_a0;
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
              Dafny.ISequence<Dafny.Rune> _3286___mcc_h134 = _source132.dtor_TypeArg_i_a0;
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
            DAST._IType _3287___mcc_h136 = _source129.dtor_baseType;
            DAST._INewtypeRange _3288___mcc_h137 = _source129.dtor_range;
            bool _3289___mcc_h138 = _source129.dtor_erase;
            Dafny.ISequence<DAST._IAttribute> _3290___mcc_h139 = _source129.dtor_attributes;
            DAST._IType _source134 = _3218___mcc_h1;
            if (_source134.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3291___mcc_h152 = _source134.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3292___mcc_h153 = _source134.dtor_typeArgs;
              DAST._IResolvedType _3293___mcc_h154 = _source134.dtor_resolved;
              DAST._IResolvedType _source135 = _3293___mcc_h154;
              if (_source135.is_Datatype) {
                DAST._IDatatypeType _3294___mcc_h161 = _source135.dtor_datatypeType;
                Dafny.ISequence<DAST._IAttribute> _3295_attributes = _3290___mcc_h139;
                bool _3296_erase = _3289___mcc_h138;
                DAST._INewtypeRange _3297_range = _3288___mcc_h137;
                DAST._IType _3298_b = _3287___mcc_h136;
                {
                  RAST._IExpr _out392;
                  DCOMP._IOwnership _out393;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out394;
                  (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out392, out _out393, out _out394);
                  r = _out392;
                  resultingOwnership = _out393;
                  readIdents = _out394;
                }
              } else if (_source135.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3299___mcc_h164 = _source135.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3300___mcc_h165 = _source135.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3301_attributes = _3290___mcc_h139;
                bool _3302_erase = _3289___mcc_h138;
                DAST._INewtypeRange _3303_range = _3288___mcc_h137;
                DAST._IType _3304_b = _3287___mcc_h136;
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
                DAST._IType _3305___mcc_h170 = _source135.dtor_baseType;
                DAST._INewtypeRange _3306___mcc_h171 = _source135.dtor_range;
                bool _3307___mcc_h172 = _source135.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3308___mcc_h173 = _source135.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3309_attributes = _3308___mcc_h173;
                bool _3310_erase = _3307___mcc_h172;
                DAST._INewtypeRange _3311_range = _3306___mcc_h171;
                DAST._IType _3312_b = _3305___mcc_h170;
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
            } else if (_source134.is_Nullable) {
              DAST._IType _3313___mcc_h182 = _source134.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out401;
                DCOMP._IOwnership _out402;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out401, out _out402, out _out403);
                r = _out401;
                resultingOwnership = _out402;
                readIdents = _out403;
              }
            } else if (_source134.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3314___mcc_h185 = _source134.dtor_Tuple_i_a0;
              Dafny.ISequence<DAST._IAttribute> _3315_attributes = _3290___mcc_h139;
              bool _3316_erase = _3289___mcc_h138;
              DAST._INewtypeRange _3317_range = _3288___mcc_h137;
              DAST._IType _3318_b = _3287___mcc_h136;
              {
                RAST._IExpr _out404;
                DCOMP._IOwnership _out405;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out406;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out404, out _out405, out _out406);
                r = _out404;
                resultingOwnership = _out405;
                readIdents = _out406;
              }
            } else if (_source134.is_Array) {
              DAST._IType _3319___mcc_h188 = _source134.dtor_element;
              BigInteger _3320___mcc_h189 = _source134.dtor_dims;
              Dafny.ISequence<DAST._IAttribute> _3321_attributes = _3290___mcc_h139;
              bool _3322_erase = _3289___mcc_h138;
              DAST._INewtypeRange _3323_range = _3288___mcc_h137;
              DAST._IType _3324_b = _3287___mcc_h136;
              {
                RAST._IExpr _out407;
                DCOMP._IOwnership _out408;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out407, out _out408, out _out409);
                r = _out407;
                resultingOwnership = _out408;
                readIdents = _out409;
              }
            } else if (_source134.is_Seq) {
              DAST._IType _3325___mcc_h194 = _source134.dtor_element;
              Dafny.ISequence<DAST._IAttribute> _3326_attributes = _3290___mcc_h139;
              bool _3327_erase = _3289___mcc_h138;
              DAST._INewtypeRange _3328_range = _3288___mcc_h137;
              DAST._IType _3329_b = _3287___mcc_h136;
              {
                RAST._IExpr _out410;
                DCOMP._IOwnership _out411;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out412;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out410, out _out411, out _out412);
                r = _out410;
                resultingOwnership = _out411;
                readIdents = _out412;
              }
            } else if (_source134.is_Set) {
              DAST._IType _3330___mcc_h197 = _source134.dtor_element;
              Dafny.ISequence<DAST._IAttribute> _3331_attributes = _3290___mcc_h139;
              bool _3332_erase = _3289___mcc_h138;
              DAST._INewtypeRange _3333_range = _3288___mcc_h137;
              DAST._IType _3334_b = _3287___mcc_h136;
              {
                RAST._IExpr _out413;
                DCOMP._IOwnership _out414;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out415;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out413, out _out414, out _out415);
                r = _out413;
                resultingOwnership = _out414;
                readIdents = _out415;
              }
            } else if (_source134.is_Multiset) {
              DAST._IType _3335___mcc_h200 = _source134.dtor_element;
              Dafny.ISequence<DAST._IAttribute> _3336_attributes = _3290___mcc_h139;
              bool _3337_erase = _3289___mcc_h138;
              DAST._INewtypeRange _3338_range = _3288___mcc_h137;
              DAST._IType _3339_b = _3287___mcc_h136;
              {
                RAST._IExpr _out416;
                DCOMP._IOwnership _out417;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out418;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out416, out _out417, out _out418);
                r = _out416;
                resultingOwnership = _out417;
                readIdents = _out418;
              }
            } else if (_source134.is_Map) {
              DAST._IType _3340___mcc_h203 = _source134.dtor_key;
              DAST._IType _3341___mcc_h204 = _source134.dtor_value;
              Dafny.ISequence<DAST._IAttribute> _3342_attributes = _3290___mcc_h139;
              bool _3343_erase = _3289___mcc_h138;
              DAST._INewtypeRange _3344_range = _3288___mcc_h137;
              DAST._IType _3345_b = _3287___mcc_h136;
              {
                RAST._IExpr _out419;
                DCOMP._IOwnership _out420;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out421;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out419, out _out420, out _out421);
                r = _out419;
                resultingOwnership = _out420;
                readIdents = _out421;
              }
            } else if (_source134.is_SetBuilder) {
              DAST._IType _3346___mcc_h209 = _source134.dtor_element;
              Dafny.ISequence<DAST._IAttribute> _3347_attributes = _3290___mcc_h139;
              bool _3348_erase = _3289___mcc_h138;
              DAST._INewtypeRange _3349_range = _3288___mcc_h137;
              DAST._IType _3350_b = _3287___mcc_h136;
              {
                RAST._IExpr _out422;
                DCOMP._IOwnership _out423;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out424;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out422, out _out423, out _out424);
                r = _out422;
                resultingOwnership = _out423;
                readIdents = _out424;
              }
            } else if (_source134.is_MapBuilder) {
              DAST._IType _3351___mcc_h212 = _source134.dtor_key;
              DAST._IType _3352___mcc_h213 = _source134.dtor_value;
              Dafny.ISequence<DAST._IAttribute> _3353_attributes = _3290___mcc_h139;
              bool _3354_erase = _3289___mcc_h138;
              DAST._INewtypeRange _3355_range = _3288___mcc_h137;
              DAST._IType _3356_b = _3287___mcc_h136;
              {
                RAST._IExpr _out425;
                DCOMP._IOwnership _out426;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out427;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out425, out _out426, out _out427);
                r = _out425;
                resultingOwnership = _out426;
                readIdents = _out427;
              }
            } else if (_source134.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3357___mcc_h218 = _source134.dtor_args;
              DAST._IType _3358___mcc_h219 = _source134.dtor_result;
              Dafny.ISequence<DAST._IAttribute> _3359_attributes = _3290___mcc_h139;
              bool _3360_erase = _3289___mcc_h138;
              DAST._INewtypeRange _3361_range = _3288___mcc_h137;
              DAST._IType _3362_b = _3287___mcc_h136;
              {
                RAST._IExpr _out428;
                DCOMP._IOwnership _out429;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out430;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out428, out _out429, out _out430);
                r = _out428;
                resultingOwnership = _out429;
                readIdents = _out430;
              }
            } else if (_source134.is_Primitive) {
              DAST._IPrimitive _3363___mcc_h224 = _source134.dtor_Primitive_i_a0;
              Dafny.ISequence<DAST._IAttribute> _3364_attributes = _3290___mcc_h139;
              bool _3365_erase = _3289___mcc_h138;
              DAST._INewtypeRange _3366_range = _3288___mcc_h137;
              DAST._IType _3367_b = _3287___mcc_h136;
              {
                RAST._IExpr _out431;
                DCOMP._IOwnership _out432;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out433;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out431, out _out432, out _out433);
                r = _out431;
                resultingOwnership = _out432;
                readIdents = _out433;
              }
            } else if (_source134.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3368___mcc_h227 = _source134.dtor_Passthrough_i_a0;
              Dafny.ISequence<DAST._IAttribute> _3369_attributes = _3290___mcc_h139;
              bool _3370_erase = _3289___mcc_h138;
              DAST._INewtypeRange _3371_range = _3288___mcc_h137;
              DAST._IType _3372_b = _3287___mcc_h136;
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
              Dafny.ISequence<Dafny.Rune> _3373___mcc_h230 = _source134.dtor_TypeArg_i_a0;
              Dafny.ISequence<DAST._IAttribute> _3374_attributes = _3290___mcc_h139;
              bool _3375_erase = _3289___mcc_h138;
              DAST._INewtypeRange _3376_range = _3288___mcc_h137;
              DAST._IType _3377_b = _3287___mcc_h136;
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
        } else if (_source128.is_Nullable) {
          DAST._IType _3378___mcc_h233 = _source128.dtor_Nullable_i_a0;
          DAST._IType _source136 = _3218___mcc_h1;
          if (_source136.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3379___mcc_h237 = _source136.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3380___mcc_h238 = _source136.dtor_typeArgs;
            DAST._IResolvedType _3381___mcc_h239 = _source136.dtor_resolved;
            DAST._IResolvedType _source137 = _3381___mcc_h239;
            if (_source137.is_Datatype) {
              DAST._IDatatypeType _3382___mcc_h246 = _source137.dtor_datatypeType;
              {
                RAST._IExpr _out440;
                DCOMP._IOwnership _out441;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out442;
                (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out440, out _out441, out _out442);
                r = _out440;
                resultingOwnership = _out441;
                readIdents = _out442;
              }
            } else if (_source137.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3383___mcc_h249 = _source137.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3384___mcc_h250 = _source137.dtor_attributes;
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
              DAST._IType _3385___mcc_h255 = _source137.dtor_baseType;
              DAST._INewtypeRange _3386___mcc_h256 = _source137.dtor_range;
              bool _3387___mcc_h257 = _source137.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3388___mcc_h258 = _source137.dtor_attributes;
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
          } else if (_source136.is_Nullable) {
            DAST._IType _3389___mcc_h267 = _source136.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out449;
              DCOMP._IOwnership _out450;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out449, out _out450, out _out451);
              r = _out449;
              resultingOwnership = _out450;
              readIdents = _out451;
            }
          } else if (_source136.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3390___mcc_h270 = _source136.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out452;
              DCOMP._IOwnership _out453;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out454;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out452, out _out453, out _out454);
              r = _out452;
              resultingOwnership = _out453;
              readIdents = _out454;
            }
          } else if (_source136.is_Array) {
            DAST._IType _3391___mcc_h273 = _source136.dtor_element;
            BigInteger _3392___mcc_h274 = _source136.dtor_dims;
            {
              RAST._IExpr _out455;
              DCOMP._IOwnership _out456;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out457;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out455, out _out456, out _out457);
              r = _out455;
              resultingOwnership = _out456;
              readIdents = _out457;
            }
          } else if (_source136.is_Seq) {
            DAST._IType _3393___mcc_h279 = _source136.dtor_element;
            {
              RAST._IExpr _out458;
              DCOMP._IOwnership _out459;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out460;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out458, out _out459, out _out460);
              r = _out458;
              resultingOwnership = _out459;
              readIdents = _out460;
            }
          } else if (_source136.is_Set) {
            DAST._IType _3394___mcc_h282 = _source136.dtor_element;
            {
              RAST._IExpr _out461;
              DCOMP._IOwnership _out462;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out463;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out461, out _out462, out _out463);
              r = _out461;
              resultingOwnership = _out462;
              readIdents = _out463;
            }
          } else if (_source136.is_Multiset) {
            DAST._IType _3395___mcc_h285 = _source136.dtor_element;
            {
              RAST._IExpr _out464;
              DCOMP._IOwnership _out465;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out466;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out464, out _out465, out _out466);
              r = _out464;
              resultingOwnership = _out465;
              readIdents = _out466;
            }
          } else if (_source136.is_Map) {
            DAST._IType _3396___mcc_h288 = _source136.dtor_key;
            DAST._IType _3397___mcc_h289 = _source136.dtor_value;
            {
              RAST._IExpr _out467;
              DCOMP._IOwnership _out468;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out469;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out467, out _out468, out _out469);
              r = _out467;
              resultingOwnership = _out468;
              readIdents = _out469;
            }
          } else if (_source136.is_SetBuilder) {
            DAST._IType _3398___mcc_h294 = _source136.dtor_element;
            {
              RAST._IExpr _out470;
              DCOMP._IOwnership _out471;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out472;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out470, out _out471, out _out472);
              r = _out470;
              resultingOwnership = _out471;
              readIdents = _out472;
            }
          } else if (_source136.is_MapBuilder) {
            DAST._IType _3399___mcc_h297 = _source136.dtor_key;
            DAST._IType _3400___mcc_h298 = _source136.dtor_value;
            {
              RAST._IExpr _out473;
              DCOMP._IOwnership _out474;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out475;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out473, out _out474, out _out475);
              r = _out473;
              resultingOwnership = _out474;
              readIdents = _out475;
            }
          } else if (_source136.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3401___mcc_h303 = _source136.dtor_args;
            DAST._IType _3402___mcc_h304 = _source136.dtor_result;
            {
              RAST._IExpr _out476;
              DCOMP._IOwnership _out477;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out478;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out476, out _out477, out _out478);
              r = _out476;
              resultingOwnership = _out477;
              readIdents = _out478;
            }
          } else if (_source136.is_Primitive) {
            DAST._IPrimitive _3403___mcc_h309 = _source136.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out479;
              DCOMP._IOwnership _out480;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out481;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out479, out _out480, out _out481);
              r = _out479;
              resultingOwnership = _out480;
              readIdents = _out481;
            }
          } else if (_source136.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3404___mcc_h312 = _source136.dtor_Passthrough_i_a0;
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
            Dafny.ISequence<Dafny.Rune> _3405___mcc_h315 = _source136.dtor_TypeArg_i_a0;
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
        } else if (_source128.is_Tuple) {
          Dafny.ISequence<DAST._IType> _3406___mcc_h318 = _source128.dtor_Tuple_i_a0;
          DAST._IType _source138 = _3218___mcc_h1;
          if (_source138.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3407___mcc_h322 = _source138.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3408___mcc_h323 = _source138.dtor_typeArgs;
            DAST._IResolvedType _3409___mcc_h324 = _source138.dtor_resolved;
            DAST._IResolvedType _source139 = _3409___mcc_h324;
            if (_source139.is_Datatype) {
              DAST._IDatatypeType _3410___mcc_h328 = _source139.dtor_datatypeType;
              {
                RAST._IExpr _out488;
                DCOMP._IOwnership _out489;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out490;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out488, out _out489, out _out490);
                r = _out488;
                resultingOwnership = _out489;
                readIdents = _out490;
              }
            } else if (_source139.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3411___mcc_h330 = _source139.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3412___mcc_h331 = _source139.dtor_attributes;
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
              DAST._IType _3413___mcc_h334 = _source139.dtor_baseType;
              DAST._INewtypeRange _3414___mcc_h335 = _source139.dtor_range;
              bool _3415___mcc_h336 = _source139.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3416___mcc_h337 = _source139.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3417_attributes = _3416___mcc_h337;
              bool _3418_erase = _3415___mcc_h336;
              DAST._INewtypeRange _3419_range = _3414___mcc_h335;
              DAST._IType _3420_b = _3413___mcc_h334;
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
          } else if (_source138.is_Nullable) {
            DAST._IType _3421___mcc_h342 = _source138.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out497;
              DCOMP._IOwnership _out498;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out499;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out497, out _out498, out _out499);
              r = _out497;
              resultingOwnership = _out498;
              readIdents = _out499;
            }
          } else if (_source138.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3422___mcc_h344 = _source138.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out500;
              DCOMP._IOwnership _out501;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out502;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out500, out _out501, out _out502);
              r = _out500;
              resultingOwnership = _out501;
              readIdents = _out502;
            }
          } else if (_source138.is_Array) {
            DAST._IType _3423___mcc_h346 = _source138.dtor_element;
            BigInteger _3424___mcc_h347 = _source138.dtor_dims;
            {
              RAST._IExpr _out503;
              DCOMP._IOwnership _out504;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out505;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out503, out _out504, out _out505);
              r = _out503;
              resultingOwnership = _out504;
              readIdents = _out505;
            }
          } else if (_source138.is_Seq) {
            DAST._IType _3425___mcc_h350 = _source138.dtor_element;
            {
              RAST._IExpr _out506;
              DCOMP._IOwnership _out507;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out508;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out506, out _out507, out _out508);
              r = _out506;
              resultingOwnership = _out507;
              readIdents = _out508;
            }
          } else if (_source138.is_Set) {
            DAST._IType _3426___mcc_h352 = _source138.dtor_element;
            {
              RAST._IExpr _out509;
              DCOMP._IOwnership _out510;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out511;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out509, out _out510, out _out511);
              r = _out509;
              resultingOwnership = _out510;
              readIdents = _out511;
            }
          } else if (_source138.is_Multiset) {
            DAST._IType _3427___mcc_h354 = _source138.dtor_element;
            {
              RAST._IExpr _out512;
              DCOMP._IOwnership _out513;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out514;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out512, out _out513, out _out514);
              r = _out512;
              resultingOwnership = _out513;
              readIdents = _out514;
            }
          } else if (_source138.is_Map) {
            DAST._IType _3428___mcc_h356 = _source138.dtor_key;
            DAST._IType _3429___mcc_h357 = _source138.dtor_value;
            {
              RAST._IExpr _out515;
              DCOMP._IOwnership _out516;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out517;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out515, out _out516, out _out517);
              r = _out515;
              resultingOwnership = _out516;
              readIdents = _out517;
            }
          } else if (_source138.is_SetBuilder) {
            DAST._IType _3430___mcc_h360 = _source138.dtor_element;
            {
              RAST._IExpr _out518;
              DCOMP._IOwnership _out519;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out520;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out518, out _out519, out _out520);
              r = _out518;
              resultingOwnership = _out519;
              readIdents = _out520;
            }
          } else if (_source138.is_MapBuilder) {
            DAST._IType _3431___mcc_h362 = _source138.dtor_key;
            DAST._IType _3432___mcc_h363 = _source138.dtor_value;
            {
              RAST._IExpr _out521;
              DCOMP._IOwnership _out522;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out523;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out521, out _out522, out _out523);
              r = _out521;
              resultingOwnership = _out522;
              readIdents = _out523;
            }
          } else if (_source138.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3433___mcc_h366 = _source138.dtor_args;
            DAST._IType _3434___mcc_h367 = _source138.dtor_result;
            {
              RAST._IExpr _out524;
              DCOMP._IOwnership _out525;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out526;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out524, out _out525, out _out526);
              r = _out524;
              resultingOwnership = _out525;
              readIdents = _out526;
            }
          } else if (_source138.is_Primitive) {
            DAST._IPrimitive _3435___mcc_h370 = _source138.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out527;
              DCOMP._IOwnership _out528;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out529;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out527, out _out528, out _out529);
              r = _out527;
              resultingOwnership = _out528;
              readIdents = _out529;
            }
          } else if (_source138.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3436___mcc_h372 = _source138.dtor_Passthrough_i_a0;
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
            Dafny.ISequence<Dafny.Rune> _3437___mcc_h374 = _source138.dtor_TypeArg_i_a0;
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
        } else if (_source128.is_Array) {
          DAST._IType _3438___mcc_h376 = _source128.dtor_element;
          BigInteger _3439___mcc_h377 = _source128.dtor_dims;
          DAST._IType _source140 = _3218___mcc_h1;
          if (_source140.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3440___mcc_h384 = _source140.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3441___mcc_h385 = _source140.dtor_typeArgs;
            DAST._IResolvedType _3442___mcc_h386 = _source140.dtor_resolved;
            DAST._IResolvedType _source141 = _3442___mcc_h386;
            if (_source141.is_Datatype) {
              DAST._IDatatypeType _3443___mcc_h390 = _source141.dtor_datatypeType;
              {
                RAST._IExpr _out536;
                DCOMP._IOwnership _out537;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out538;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out536, out _out537, out _out538);
                r = _out536;
                resultingOwnership = _out537;
                readIdents = _out538;
              }
            } else if (_source141.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3444___mcc_h392 = _source141.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3445___mcc_h393 = _source141.dtor_attributes;
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
              DAST._IType _3446___mcc_h396 = _source141.dtor_baseType;
              DAST._INewtypeRange _3447___mcc_h397 = _source141.dtor_range;
              bool _3448___mcc_h398 = _source141.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3449___mcc_h399 = _source141.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3450_attributes = _3449___mcc_h399;
              bool _3451_erase = _3448___mcc_h398;
              DAST._INewtypeRange _3452_range = _3447___mcc_h397;
              DAST._IType _3453_b = _3446___mcc_h396;
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
          } else if (_source140.is_Nullable) {
            DAST._IType _3454___mcc_h404 = _source140.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out545;
              DCOMP._IOwnership _out546;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out547;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out545, out _out546, out _out547);
              r = _out545;
              resultingOwnership = _out546;
              readIdents = _out547;
            }
          } else if (_source140.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3455___mcc_h406 = _source140.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out548;
              DCOMP._IOwnership _out549;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out550;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out548, out _out549, out _out550);
              r = _out548;
              resultingOwnership = _out549;
              readIdents = _out550;
            }
          } else if (_source140.is_Array) {
            DAST._IType _3456___mcc_h408 = _source140.dtor_element;
            BigInteger _3457___mcc_h409 = _source140.dtor_dims;
            {
              RAST._IExpr _out551;
              DCOMP._IOwnership _out552;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out553;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out551, out _out552, out _out553);
              r = _out551;
              resultingOwnership = _out552;
              readIdents = _out553;
            }
          } else if (_source140.is_Seq) {
            DAST._IType _3458___mcc_h412 = _source140.dtor_element;
            {
              RAST._IExpr _out554;
              DCOMP._IOwnership _out555;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out556;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out554, out _out555, out _out556);
              r = _out554;
              resultingOwnership = _out555;
              readIdents = _out556;
            }
          } else if (_source140.is_Set) {
            DAST._IType _3459___mcc_h414 = _source140.dtor_element;
            {
              RAST._IExpr _out557;
              DCOMP._IOwnership _out558;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out559;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out557, out _out558, out _out559);
              r = _out557;
              resultingOwnership = _out558;
              readIdents = _out559;
            }
          } else if (_source140.is_Multiset) {
            DAST._IType _3460___mcc_h416 = _source140.dtor_element;
            {
              RAST._IExpr _out560;
              DCOMP._IOwnership _out561;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out562;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out560, out _out561, out _out562);
              r = _out560;
              resultingOwnership = _out561;
              readIdents = _out562;
            }
          } else if (_source140.is_Map) {
            DAST._IType _3461___mcc_h418 = _source140.dtor_key;
            DAST._IType _3462___mcc_h419 = _source140.dtor_value;
            {
              RAST._IExpr _out563;
              DCOMP._IOwnership _out564;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out565;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out563, out _out564, out _out565);
              r = _out563;
              resultingOwnership = _out564;
              readIdents = _out565;
            }
          } else if (_source140.is_SetBuilder) {
            DAST._IType _3463___mcc_h422 = _source140.dtor_element;
            {
              RAST._IExpr _out566;
              DCOMP._IOwnership _out567;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out568;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out566, out _out567, out _out568);
              r = _out566;
              resultingOwnership = _out567;
              readIdents = _out568;
            }
          } else if (_source140.is_MapBuilder) {
            DAST._IType _3464___mcc_h424 = _source140.dtor_key;
            DAST._IType _3465___mcc_h425 = _source140.dtor_value;
            {
              RAST._IExpr _out569;
              DCOMP._IOwnership _out570;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out571;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out569, out _out570, out _out571);
              r = _out569;
              resultingOwnership = _out570;
              readIdents = _out571;
            }
          } else if (_source140.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3466___mcc_h428 = _source140.dtor_args;
            DAST._IType _3467___mcc_h429 = _source140.dtor_result;
            {
              RAST._IExpr _out572;
              DCOMP._IOwnership _out573;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out574;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out572, out _out573, out _out574);
              r = _out572;
              resultingOwnership = _out573;
              readIdents = _out574;
            }
          } else if (_source140.is_Primitive) {
            DAST._IPrimitive _3468___mcc_h432 = _source140.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out575;
              DCOMP._IOwnership _out576;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out577;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out575, out _out576, out _out577);
              r = _out575;
              resultingOwnership = _out576;
              readIdents = _out577;
            }
          } else if (_source140.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3469___mcc_h434 = _source140.dtor_Passthrough_i_a0;
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
            Dafny.ISequence<Dafny.Rune> _3470___mcc_h436 = _source140.dtor_TypeArg_i_a0;
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
        } else if (_source128.is_Seq) {
          DAST._IType _3471___mcc_h438 = _source128.dtor_element;
          DAST._IType _source142 = _3218___mcc_h1;
          if (_source142.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3472___mcc_h442 = _source142.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3473___mcc_h443 = _source142.dtor_typeArgs;
            DAST._IResolvedType _3474___mcc_h444 = _source142.dtor_resolved;
            DAST._IResolvedType _source143 = _3474___mcc_h444;
            if (_source143.is_Datatype) {
              DAST._IDatatypeType _3475___mcc_h448 = _source143.dtor_datatypeType;
              {
                RAST._IExpr _out584;
                DCOMP._IOwnership _out585;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out586;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out584, out _out585, out _out586);
                r = _out584;
                resultingOwnership = _out585;
                readIdents = _out586;
              }
            } else if (_source143.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3476___mcc_h450 = _source143.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3477___mcc_h451 = _source143.dtor_attributes;
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
              DAST._IType _3478___mcc_h454 = _source143.dtor_baseType;
              DAST._INewtypeRange _3479___mcc_h455 = _source143.dtor_range;
              bool _3480___mcc_h456 = _source143.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3481___mcc_h457 = _source143.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3482_attributes = _3481___mcc_h457;
              bool _3483_erase = _3480___mcc_h456;
              DAST._INewtypeRange _3484_range = _3479___mcc_h455;
              DAST._IType _3485_b = _3478___mcc_h454;
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
          } else if (_source142.is_Nullable) {
            DAST._IType _3486___mcc_h462 = _source142.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out593;
              DCOMP._IOwnership _out594;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out595;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out593, out _out594, out _out595);
              r = _out593;
              resultingOwnership = _out594;
              readIdents = _out595;
            }
          } else if (_source142.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3487___mcc_h464 = _source142.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out596;
              DCOMP._IOwnership _out597;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out598;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out596, out _out597, out _out598);
              r = _out596;
              resultingOwnership = _out597;
              readIdents = _out598;
            }
          } else if (_source142.is_Array) {
            DAST._IType _3488___mcc_h466 = _source142.dtor_element;
            BigInteger _3489___mcc_h467 = _source142.dtor_dims;
            {
              RAST._IExpr _out599;
              DCOMP._IOwnership _out600;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out601;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out599, out _out600, out _out601);
              r = _out599;
              resultingOwnership = _out600;
              readIdents = _out601;
            }
          } else if (_source142.is_Seq) {
            DAST._IType _3490___mcc_h470 = _source142.dtor_element;
            {
              RAST._IExpr _out602;
              DCOMP._IOwnership _out603;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out604;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out602, out _out603, out _out604);
              r = _out602;
              resultingOwnership = _out603;
              readIdents = _out604;
            }
          } else if (_source142.is_Set) {
            DAST._IType _3491___mcc_h472 = _source142.dtor_element;
            {
              RAST._IExpr _out605;
              DCOMP._IOwnership _out606;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out607;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out605, out _out606, out _out607);
              r = _out605;
              resultingOwnership = _out606;
              readIdents = _out607;
            }
          } else if (_source142.is_Multiset) {
            DAST._IType _3492___mcc_h474 = _source142.dtor_element;
            {
              RAST._IExpr _out608;
              DCOMP._IOwnership _out609;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out610;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out608, out _out609, out _out610);
              r = _out608;
              resultingOwnership = _out609;
              readIdents = _out610;
            }
          } else if (_source142.is_Map) {
            DAST._IType _3493___mcc_h476 = _source142.dtor_key;
            DAST._IType _3494___mcc_h477 = _source142.dtor_value;
            {
              RAST._IExpr _out611;
              DCOMP._IOwnership _out612;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out613;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out611, out _out612, out _out613);
              r = _out611;
              resultingOwnership = _out612;
              readIdents = _out613;
            }
          } else if (_source142.is_SetBuilder) {
            DAST._IType _3495___mcc_h480 = _source142.dtor_element;
            {
              RAST._IExpr _out614;
              DCOMP._IOwnership _out615;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out616;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out614, out _out615, out _out616);
              r = _out614;
              resultingOwnership = _out615;
              readIdents = _out616;
            }
          } else if (_source142.is_MapBuilder) {
            DAST._IType _3496___mcc_h482 = _source142.dtor_key;
            DAST._IType _3497___mcc_h483 = _source142.dtor_value;
            {
              RAST._IExpr _out617;
              DCOMP._IOwnership _out618;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out619;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out617, out _out618, out _out619);
              r = _out617;
              resultingOwnership = _out618;
              readIdents = _out619;
            }
          } else if (_source142.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3498___mcc_h486 = _source142.dtor_args;
            DAST._IType _3499___mcc_h487 = _source142.dtor_result;
            {
              RAST._IExpr _out620;
              DCOMP._IOwnership _out621;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out620, out _out621, out _out622);
              r = _out620;
              resultingOwnership = _out621;
              readIdents = _out622;
            }
          } else if (_source142.is_Primitive) {
            DAST._IPrimitive _3500___mcc_h490 = _source142.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out623;
              DCOMP._IOwnership _out624;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out625;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out623, out _out624, out _out625);
              r = _out623;
              resultingOwnership = _out624;
              readIdents = _out625;
            }
          } else if (_source142.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3501___mcc_h492 = _source142.dtor_Passthrough_i_a0;
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
            Dafny.ISequence<Dafny.Rune> _3502___mcc_h494 = _source142.dtor_TypeArg_i_a0;
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
        } else if (_source128.is_Set) {
          DAST._IType _3503___mcc_h496 = _source128.dtor_element;
          DAST._IType _source144 = _3218___mcc_h1;
          if (_source144.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3504___mcc_h500 = _source144.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3505___mcc_h501 = _source144.dtor_typeArgs;
            DAST._IResolvedType _3506___mcc_h502 = _source144.dtor_resolved;
            DAST._IResolvedType _source145 = _3506___mcc_h502;
            if (_source145.is_Datatype) {
              DAST._IDatatypeType _3507___mcc_h506 = _source145.dtor_datatypeType;
              {
                RAST._IExpr _out632;
                DCOMP._IOwnership _out633;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out634;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out632, out _out633, out _out634);
                r = _out632;
                resultingOwnership = _out633;
                readIdents = _out634;
              }
            } else if (_source145.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3508___mcc_h508 = _source145.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3509___mcc_h509 = _source145.dtor_attributes;
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
              DAST._IType _3510___mcc_h512 = _source145.dtor_baseType;
              DAST._INewtypeRange _3511___mcc_h513 = _source145.dtor_range;
              bool _3512___mcc_h514 = _source145.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3513___mcc_h515 = _source145.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3514_attributes = _3513___mcc_h515;
              bool _3515_erase = _3512___mcc_h514;
              DAST._INewtypeRange _3516_range = _3511___mcc_h513;
              DAST._IType _3517_b = _3510___mcc_h512;
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
          } else if (_source144.is_Nullable) {
            DAST._IType _3518___mcc_h520 = _source144.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out641;
              DCOMP._IOwnership _out642;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out643;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out641, out _out642, out _out643);
              r = _out641;
              resultingOwnership = _out642;
              readIdents = _out643;
            }
          } else if (_source144.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3519___mcc_h522 = _source144.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out644;
              DCOMP._IOwnership _out645;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out646;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out644, out _out645, out _out646);
              r = _out644;
              resultingOwnership = _out645;
              readIdents = _out646;
            }
          } else if (_source144.is_Array) {
            DAST._IType _3520___mcc_h524 = _source144.dtor_element;
            BigInteger _3521___mcc_h525 = _source144.dtor_dims;
            {
              RAST._IExpr _out647;
              DCOMP._IOwnership _out648;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out649;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out647, out _out648, out _out649);
              r = _out647;
              resultingOwnership = _out648;
              readIdents = _out649;
            }
          } else if (_source144.is_Seq) {
            DAST._IType _3522___mcc_h528 = _source144.dtor_element;
            {
              RAST._IExpr _out650;
              DCOMP._IOwnership _out651;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out652;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out650, out _out651, out _out652);
              r = _out650;
              resultingOwnership = _out651;
              readIdents = _out652;
            }
          } else if (_source144.is_Set) {
            DAST._IType _3523___mcc_h530 = _source144.dtor_element;
            {
              RAST._IExpr _out653;
              DCOMP._IOwnership _out654;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out653, out _out654, out _out655);
              r = _out653;
              resultingOwnership = _out654;
              readIdents = _out655;
            }
          } else if (_source144.is_Multiset) {
            DAST._IType _3524___mcc_h532 = _source144.dtor_element;
            {
              RAST._IExpr _out656;
              DCOMP._IOwnership _out657;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out658;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out656, out _out657, out _out658);
              r = _out656;
              resultingOwnership = _out657;
              readIdents = _out658;
            }
          } else if (_source144.is_Map) {
            DAST._IType _3525___mcc_h534 = _source144.dtor_key;
            DAST._IType _3526___mcc_h535 = _source144.dtor_value;
            {
              RAST._IExpr _out659;
              DCOMP._IOwnership _out660;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out661;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out659, out _out660, out _out661);
              r = _out659;
              resultingOwnership = _out660;
              readIdents = _out661;
            }
          } else if (_source144.is_SetBuilder) {
            DAST._IType _3527___mcc_h538 = _source144.dtor_element;
            {
              RAST._IExpr _out662;
              DCOMP._IOwnership _out663;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out664;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out662, out _out663, out _out664);
              r = _out662;
              resultingOwnership = _out663;
              readIdents = _out664;
            }
          } else if (_source144.is_MapBuilder) {
            DAST._IType _3528___mcc_h540 = _source144.dtor_key;
            DAST._IType _3529___mcc_h541 = _source144.dtor_value;
            {
              RAST._IExpr _out665;
              DCOMP._IOwnership _out666;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out667;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out665, out _out666, out _out667);
              r = _out665;
              resultingOwnership = _out666;
              readIdents = _out667;
            }
          } else if (_source144.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3530___mcc_h544 = _source144.dtor_args;
            DAST._IType _3531___mcc_h545 = _source144.dtor_result;
            {
              RAST._IExpr _out668;
              DCOMP._IOwnership _out669;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out670;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out668, out _out669, out _out670);
              r = _out668;
              resultingOwnership = _out669;
              readIdents = _out670;
            }
          } else if (_source144.is_Primitive) {
            DAST._IPrimitive _3532___mcc_h548 = _source144.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out671;
              DCOMP._IOwnership _out672;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out673;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out671, out _out672, out _out673);
              r = _out671;
              resultingOwnership = _out672;
              readIdents = _out673;
            }
          } else if (_source144.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3533___mcc_h550 = _source144.dtor_Passthrough_i_a0;
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
            Dafny.ISequence<Dafny.Rune> _3534___mcc_h552 = _source144.dtor_TypeArg_i_a0;
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
        } else if (_source128.is_Multiset) {
          DAST._IType _3535___mcc_h554 = _source128.dtor_element;
          DAST._IType _source146 = _3218___mcc_h1;
          if (_source146.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3536___mcc_h558 = _source146.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3537___mcc_h559 = _source146.dtor_typeArgs;
            DAST._IResolvedType _3538___mcc_h560 = _source146.dtor_resolved;
            DAST._IResolvedType _source147 = _3538___mcc_h560;
            if (_source147.is_Datatype) {
              DAST._IDatatypeType _3539___mcc_h564 = _source147.dtor_datatypeType;
              {
                RAST._IExpr _out680;
                DCOMP._IOwnership _out681;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out682;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out680, out _out681, out _out682);
                r = _out680;
                resultingOwnership = _out681;
                readIdents = _out682;
              }
            } else if (_source147.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3540___mcc_h566 = _source147.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3541___mcc_h567 = _source147.dtor_attributes;
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
              DAST._IType _3542___mcc_h570 = _source147.dtor_baseType;
              DAST._INewtypeRange _3543___mcc_h571 = _source147.dtor_range;
              bool _3544___mcc_h572 = _source147.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3545___mcc_h573 = _source147.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3546_attributes = _3545___mcc_h573;
              bool _3547_erase = _3544___mcc_h572;
              DAST._INewtypeRange _3548_range = _3543___mcc_h571;
              DAST._IType _3549_b = _3542___mcc_h570;
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
          } else if (_source146.is_Nullable) {
            DAST._IType _3550___mcc_h578 = _source146.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out689;
              DCOMP._IOwnership _out690;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out691;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out689, out _out690, out _out691);
              r = _out689;
              resultingOwnership = _out690;
              readIdents = _out691;
            }
          } else if (_source146.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3551___mcc_h580 = _source146.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out692;
              DCOMP._IOwnership _out693;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out694;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out692, out _out693, out _out694);
              r = _out692;
              resultingOwnership = _out693;
              readIdents = _out694;
            }
          } else if (_source146.is_Array) {
            DAST._IType _3552___mcc_h582 = _source146.dtor_element;
            BigInteger _3553___mcc_h583 = _source146.dtor_dims;
            {
              RAST._IExpr _out695;
              DCOMP._IOwnership _out696;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out697;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out695, out _out696, out _out697);
              r = _out695;
              resultingOwnership = _out696;
              readIdents = _out697;
            }
          } else if (_source146.is_Seq) {
            DAST._IType _3554___mcc_h586 = _source146.dtor_element;
            {
              RAST._IExpr _out698;
              DCOMP._IOwnership _out699;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out700;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out698, out _out699, out _out700);
              r = _out698;
              resultingOwnership = _out699;
              readIdents = _out700;
            }
          } else if (_source146.is_Set) {
            DAST._IType _3555___mcc_h588 = _source146.dtor_element;
            {
              RAST._IExpr _out701;
              DCOMP._IOwnership _out702;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out703;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out701, out _out702, out _out703);
              r = _out701;
              resultingOwnership = _out702;
              readIdents = _out703;
            }
          } else if (_source146.is_Multiset) {
            DAST._IType _3556___mcc_h590 = _source146.dtor_element;
            {
              RAST._IExpr _out704;
              DCOMP._IOwnership _out705;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out706;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out704, out _out705, out _out706);
              r = _out704;
              resultingOwnership = _out705;
              readIdents = _out706;
            }
          } else if (_source146.is_Map) {
            DAST._IType _3557___mcc_h592 = _source146.dtor_key;
            DAST._IType _3558___mcc_h593 = _source146.dtor_value;
            {
              RAST._IExpr _out707;
              DCOMP._IOwnership _out708;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out709;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out707, out _out708, out _out709);
              r = _out707;
              resultingOwnership = _out708;
              readIdents = _out709;
            }
          } else if (_source146.is_SetBuilder) {
            DAST._IType _3559___mcc_h596 = _source146.dtor_element;
            {
              RAST._IExpr _out710;
              DCOMP._IOwnership _out711;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out712;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out710, out _out711, out _out712);
              r = _out710;
              resultingOwnership = _out711;
              readIdents = _out712;
            }
          } else if (_source146.is_MapBuilder) {
            DAST._IType _3560___mcc_h598 = _source146.dtor_key;
            DAST._IType _3561___mcc_h599 = _source146.dtor_value;
            {
              RAST._IExpr _out713;
              DCOMP._IOwnership _out714;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out715;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out713, out _out714, out _out715);
              r = _out713;
              resultingOwnership = _out714;
              readIdents = _out715;
            }
          } else if (_source146.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3562___mcc_h602 = _source146.dtor_args;
            DAST._IType _3563___mcc_h603 = _source146.dtor_result;
            {
              RAST._IExpr _out716;
              DCOMP._IOwnership _out717;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out718;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out716, out _out717, out _out718);
              r = _out716;
              resultingOwnership = _out717;
              readIdents = _out718;
            }
          } else if (_source146.is_Primitive) {
            DAST._IPrimitive _3564___mcc_h606 = _source146.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out719;
              DCOMP._IOwnership _out720;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out721;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out719, out _out720, out _out721);
              r = _out719;
              resultingOwnership = _out720;
              readIdents = _out721;
            }
          } else if (_source146.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3565___mcc_h608 = _source146.dtor_Passthrough_i_a0;
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
            Dafny.ISequence<Dafny.Rune> _3566___mcc_h610 = _source146.dtor_TypeArg_i_a0;
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
        } else if (_source128.is_Map) {
          DAST._IType _3567___mcc_h612 = _source128.dtor_key;
          DAST._IType _3568___mcc_h613 = _source128.dtor_value;
          DAST._IType _source148 = _3218___mcc_h1;
          if (_source148.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3569___mcc_h620 = _source148.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3570___mcc_h621 = _source148.dtor_typeArgs;
            DAST._IResolvedType _3571___mcc_h622 = _source148.dtor_resolved;
            DAST._IResolvedType _source149 = _3571___mcc_h622;
            if (_source149.is_Datatype) {
              DAST._IDatatypeType _3572___mcc_h626 = _source149.dtor_datatypeType;
              {
                RAST._IExpr _out728;
                DCOMP._IOwnership _out729;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out730;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out728, out _out729, out _out730);
                r = _out728;
                resultingOwnership = _out729;
                readIdents = _out730;
              }
            } else if (_source149.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3573___mcc_h628 = _source149.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3574___mcc_h629 = _source149.dtor_attributes;
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
              DAST._IType _3575___mcc_h632 = _source149.dtor_baseType;
              DAST._INewtypeRange _3576___mcc_h633 = _source149.dtor_range;
              bool _3577___mcc_h634 = _source149.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3578___mcc_h635 = _source149.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3579_attributes = _3578___mcc_h635;
              bool _3580_erase = _3577___mcc_h634;
              DAST._INewtypeRange _3581_range = _3576___mcc_h633;
              DAST._IType _3582_b = _3575___mcc_h632;
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
          } else if (_source148.is_Nullable) {
            DAST._IType _3583___mcc_h640 = _source148.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out737;
              DCOMP._IOwnership _out738;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out739;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out737, out _out738, out _out739);
              r = _out737;
              resultingOwnership = _out738;
              readIdents = _out739;
            }
          } else if (_source148.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3584___mcc_h642 = _source148.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out740;
              DCOMP._IOwnership _out741;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out742;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out740, out _out741, out _out742);
              r = _out740;
              resultingOwnership = _out741;
              readIdents = _out742;
            }
          } else if (_source148.is_Array) {
            DAST._IType _3585___mcc_h644 = _source148.dtor_element;
            BigInteger _3586___mcc_h645 = _source148.dtor_dims;
            {
              RAST._IExpr _out743;
              DCOMP._IOwnership _out744;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out745;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out743, out _out744, out _out745);
              r = _out743;
              resultingOwnership = _out744;
              readIdents = _out745;
            }
          } else if (_source148.is_Seq) {
            DAST._IType _3587___mcc_h648 = _source148.dtor_element;
            {
              RAST._IExpr _out746;
              DCOMP._IOwnership _out747;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out748;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out746, out _out747, out _out748);
              r = _out746;
              resultingOwnership = _out747;
              readIdents = _out748;
            }
          } else if (_source148.is_Set) {
            DAST._IType _3588___mcc_h650 = _source148.dtor_element;
            {
              RAST._IExpr _out749;
              DCOMP._IOwnership _out750;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out751;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out749, out _out750, out _out751);
              r = _out749;
              resultingOwnership = _out750;
              readIdents = _out751;
            }
          } else if (_source148.is_Multiset) {
            DAST._IType _3589___mcc_h652 = _source148.dtor_element;
            {
              RAST._IExpr _out752;
              DCOMP._IOwnership _out753;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out754;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out752, out _out753, out _out754);
              r = _out752;
              resultingOwnership = _out753;
              readIdents = _out754;
            }
          } else if (_source148.is_Map) {
            DAST._IType _3590___mcc_h654 = _source148.dtor_key;
            DAST._IType _3591___mcc_h655 = _source148.dtor_value;
            {
              RAST._IExpr _out755;
              DCOMP._IOwnership _out756;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out757;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out755, out _out756, out _out757);
              r = _out755;
              resultingOwnership = _out756;
              readIdents = _out757;
            }
          } else if (_source148.is_SetBuilder) {
            DAST._IType _3592___mcc_h658 = _source148.dtor_element;
            {
              RAST._IExpr _out758;
              DCOMP._IOwnership _out759;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out760;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out758, out _out759, out _out760);
              r = _out758;
              resultingOwnership = _out759;
              readIdents = _out760;
            }
          } else if (_source148.is_MapBuilder) {
            DAST._IType _3593___mcc_h660 = _source148.dtor_key;
            DAST._IType _3594___mcc_h661 = _source148.dtor_value;
            {
              RAST._IExpr _out761;
              DCOMP._IOwnership _out762;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out763;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out761, out _out762, out _out763);
              r = _out761;
              resultingOwnership = _out762;
              readIdents = _out763;
            }
          } else if (_source148.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3595___mcc_h664 = _source148.dtor_args;
            DAST._IType _3596___mcc_h665 = _source148.dtor_result;
            {
              RAST._IExpr _out764;
              DCOMP._IOwnership _out765;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out766;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out764, out _out765, out _out766);
              r = _out764;
              resultingOwnership = _out765;
              readIdents = _out766;
            }
          } else if (_source148.is_Primitive) {
            DAST._IPrimitive _3597___mcc_h668 = _source148.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out767;
              DCOMP._IOwnership _out768;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out769;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out767, out _out768, out _out769);
              r = _out767;
              resultingOwnership = _out768;
              readIdents = _out769;
            }
          } else if (_source148.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3598___mcc_h670 = _source148.dtor_Passthrough_i_a0;
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
            Dafny.ISequence<Dafny.Rune> _3599___mcc_h672 = _source148.dtor_TypeArg_i_a0;
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
        } else if (_source128.is_SetBuilder) {
          DAST._IType _3600___mcc_h674 = _source128.dtor_element;
          DAST._IType _source150 = _3218___mcc_h1;
          if (_source150.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3601___mcc_h678 = _source150.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3602___mcc_h679 = _source150.dtor_typeArgs;
            DAST._IResolvedType _3603___mcc_h680 = _source150.dtor_resolved;
            DAST._IResolvedType _source151 = _3603___mcc_h680;
            if (_source151.is_Datatype) {
              DAST._IDatatypeType _3604___mcc_h684 = _source151.dtor_datatypeType;
              {
                RAST._IExpr _out776;
                DCOMP._IOwnership _out777;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out778;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out776, out _out777, out _out778);
                r = _out776;
                resultingOwnership = _out777;
                readIdents = _out778;
              }
            } else if (_source151.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3605___mcc_h686 = _source151.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3606___mcc_h687 = _source151.dtor_attributes;
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
              DAST._IType _3607___mcc_h690 = _source151.dtor_baseType;
              DAST._INewtypeRange _3608___mcc_h691 = _source151.dtor_range;
              bool _3609___mcc_h692 = _source151.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3610___mcc_h693 = _source151.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3611_attributes = _3610___mcc_h693;
              bool _3612_erase = _3609___mcc_h692;
              DAST._INewtypeRange _3613_range = _3608___mcc_h691;
              DAST._IType _3614_b = _3607___mcc_h690;
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
          } else if (_source150.is_Nullable) {
            DAST._IType _3615___mcc_h698 = _source150.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out785;
              DCOMP._IOwnership _out786;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out787;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out785, out _out786, out _out787);
              r = _out785;
              resultingOwnership = _out786;
              readIdents = _out787;
            }
          } else if (_source150.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3616___mcc_h700 = _source150.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out788;
              DCOMP._IOwnership _out789;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out790;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out788, out _out789, out _out790);
              r = _out788;
              resultingOwnership = _out789;
              readIdents = _out790;
            }
          } else if (_source150.is_Array) {
            DAST._IType _3617___mcc_h702 = _source150.dtor_element;
            BigInteger _3618___mcc_h703 = _source150.dtor_dims;
            {
              RAST._IExpr _out791;
              DCOMP._IOwnership _out792;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out793;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out791, out _out792, out _out793);
              r = _out791;
              resultingOwnership = _out792;
              readIdents = _out793;
            }
          } else if (_source150.is_Seq) {
            DAST._IType _3619___mcc_h706 = _source150.dtor_element;
            {
              RAST._IExpr _out794;
              DCOMP._IOwnership _out795;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out796;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out794, out _out795, out _out796);
              r = _out794;
              resultingOwnership = _out795;
              readIdents = _out796;
            }
          } else if (_source150.is_Set) {
            DAST._IType _3620___mcc_h708 = _source150.dtor_element;
            {
              RAST._IExpr _out797;
              DCOMP._IOwnership _out798;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out799;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out797, out _out798, out _out799);
              r = _out797;
              resultingOwnership = _out798;
              readIdents = _out799;
            }
          } else if (_source150.is_Multiset) {
            DAST._IType _3621___mcc_h710 = _source150.dtor_element;
            {
              RAST._IExpr _out800;
              DCOMP._IOwnership _out801;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out802;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out800, out _out801, out _out802);
              r = _out800;
              resultingOwnership = _out801;
              readIdents = _out802;
            }
          } else if (_source150.is_Map) {
            DAST._IType _3622___mcc_h712 = _source150.dtor_key;
            DAST._IType _3623___mcc_h713 = _source150.dtor_value;
            {
              RAST._IExpr _out803;
              DCOMP._IOwnership _out804;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out805;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out803, out _out804, out _out805);
              r = _out803;
              resultingOwnership = _out804;
              readIdents = _out805;
            }
          } else if (_source150.is_SetBuilder) {
            DAST._IType _3624___mcc_h716 = _source150.dtor_element;
            {
              RAST._IExpr _out806;
              DCOMP._IOwnership _out807;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out808;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out806, out _out807, out _out808);
              r = _out806;
              resultingOwnership = _out807;
              readIdents = _out808;
            }
          } else if (_source150.is_MapBuilder) {
            DAST._IType _3625___mcc_h718 = _source150.dtor_key;
            DAST._IType _3626___mcc_h719 = _source150.dtor_value;
            {
              RAST._IExpr _out809;
              DCOMP._IOwnership _out810;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out811;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out809, out _out810, out _out811);
              r = _out809;
              resultingOwnership = _out810;
              readIdents = _out811;
            }
          } else if (_source150.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3627___mcc_h722 = _source150.dtor_args;
            DAST._IType _3628___mcc_h723 = _source150.dtor_result;
            {
              RAST._IExpr _out812;
              DCOMP._IOwnership _out813;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out814;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out812, out _out813, out _out814);
              r = _out812;
              resultingOwnership = _out813;
              readIdents = _out814;
            }
          } else if (_source150.is_Primitive) {
            DAST._IPrimitive _3629___mcc_h726 = _source150.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out815;
              DCOMP._IOwnership _out816;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out817;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out815, out _out816, out _out817);
              r = _out815;
              resultingOwnership = _out816;
              readIdents = _out817;
            }
          } else if (_source150.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3630___mcc_h728 = _source150.dtor_Passthrough_i_a0;
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
            Dafny.ISequence<Dafny.Rune> _3631___mcc_h730 = _source150.dtor_TypeArg_i_a0;
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
        } else if (_source128.is_MapBuilder) {
          DAST._IType _3632___mcc_h732 = _source128.dtor_key;
          DAST._IType _3633___mcc_h733 = _source128.dtor_value;
          DAST._IType _source152 = _3218___mcc_h1;
          if (_source152.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3634___mcc_h740 = _source152.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3635___mcc_h741 = _source152.dtor_typeArgs;
            DAST._IResolvedType _3636___mcc_h742 = _source152.dtor_resolved;
            DAST._IResolvedType _source153 = _3636___mcc_h742;
            if (_source153.is_Datatype) {
              DAST._IDatatypeType _3637___mcc_h746 = _source153.dtor_datatypeType;
              {
                RAST._IExpr _out824;
                DCOMP._IOwnership _out825;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out826;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out824, out _out825, out _out826);
                r = _out824;
                resultingOwnership = _out825;
                readIdents = _out826;
              }
            } else if (_source153.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3638___mcc_h748 = _source153.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3639___mcc_h749 = _source153.dtor_attributes;
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
              DAST._IType _3640___mcc_h752 = _source153.dtor_baseType;
              DAST._INewtypeRange _3641___mcc_h753 = _source153.dtor_range;
              bool _3642___mcc_h754 = _source153.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3643___mcc_h755 = _source153.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3644_attributes = _3643___mcc_h755;
              bool _3645_erase = _3642___mcc_h754;
              DAST._INewtypeRange _3646_range = _3641___mcc_h753;
              DAST._IType _3647_b = _3640___mcc_h752;
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
          } else if (_source152.is_Nullable) {
            DAST._IType _3648___mcc_h760 = _source152.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out833;
              DCOMP._IOwnership _out834;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out835;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out833, out _out834, out _out835);
              r = _out833;
              resultingOwnership = _out834;
              readIdents = _out835;
            }
          } else if (_source152.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3649___mcc_h762 = _source152.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out836;
              DCOMP._IOwnership _out837;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out838;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out836, out _out837, out _out838);
              r = _out836;
              resultingOwnership = _out837;
              readIdents = _out838;
            }
          } else if (_source152.is_Array) {
            DAST._IType _3650___mcc_h764 = _source152.dtor_element;
            BigInteger _3651___mcc_h765 = _source152.dtor_dims;
            {
              RAST._IExpr _out839;
              DCOMP._IOwnership _out840;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out841;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out839, out _out840, out _out841);
              r = _out839;
              resultingOwnership = _out840;
              readIdents = _out841;
            }
          } else if (_source152.is_Seq) {
            DAST._IType _3652___mcc_h768 = _source152.dtor_element;
            {
              RAST._IExpr _out842;
              DCOMP._IOwnership _out843;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out844;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out842, out _out843, out _out844);
              r = _out842;
              resultingOwnership = _out843;
              readIdents = _out844;
            }
          } else if (_source152.is_Set) {
            DAST._IType _3653___mcc_h770 = _source152.dtor_element;
            {
              RAST._IExpr _out845;
              DCOMP._IOwnership _out846;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out847;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out845, out _out846, out _out847);
              r = _out845;
              resultingOwnership = _out846;
              readIdents = _out847;
            }
          } else if (_source152.is_Multiset) {
            DAST._IType _3654___mcc_h772 = _source152.dtor_element;
            {
              RAST._IExpr _out848;
              DCOMP._IOwnership _out849;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out850;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out848, out _out849, out _out850);
              r = _out848;
              resultingOwnership = _out849;
              readIdents = _out850;
            }
          } else if (_source152.is_Map) {
            DAST._IType _3655___mcc_h774 = _source152.dtor_key;
            DAST._IType _3656___mcc_h775 = _source152.dtor_value;
            {
              RAST._IExpr _out851;
              DCOMP._IOwnership _out852;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out853;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out851, out _out852, out _out853);
              r = _out851;
              resultingOwnership = _out852;
              readIdents = _out853;
            }
          } else if (_source152.is_SetBuilder) {
            DAST._IType _3657___mcc_h778 = _source152.dtor_element;
            {
              RAST._IExpr _out854;
              DCOMP._IOwnership _out855;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out856;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out854, out _out855, out _out856);
              r = _out854;
              resultingOwnership = _out855;
              readIdents = _out856;
            }
          } else if (_source152.is_MapBuilder) {
            DAST._IType _3658___mcc_h780 = _source152.dtor_key;
            DAST._IType _3659___mcc_h781 = _source152.dtor_value;
            {
              RAST._IExpr _out857;
              DCOMP._IOwnership _out858;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out859;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out857, out _out858, out _out859);
              r = _out857;
              resultingOwnership = _out858;
              readIdents = _out859;
            }
          } else if (_source152.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3660___mcc_h784 = _source152.dtor_args;
            DAST._IType _3661___mcc_h785 = _source152.dtor_result;
            {
              RAST._IExpr _out860;
              DCOMP._IOwnership _out861;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out862;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out860, out _out861, out _out862);
              r = _out860;
              resultingOwnership = _out861;
              readIdents = _out862;
            }
          } else if (_source152.is_Primitive) {
            DAST._IPrimitive _3662___mcc_h788 = _source152.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out863;
              DCOMP._IOwnership _out864;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out865;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out863, out _out864, out _out865);
              r = _out863;
              resultingOwnership = _out864;
              readIdents = _out865;
            }
          } else if (_source152.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3663___mcc_h790 = _source152.dtor_Passthrough_i_a0;
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
            Dafny.ISequence<Dafny.Rune> _3664___mcc_h792 = _source152.dtor_TypeArg_i_a0;
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
        } else if (_source128.is_Arrow) {
          Dafny.ISequence<DAST._IType> _3665___mcc_h794 = _source128.dtor_args;
          DAST._IType _3666___mcc_h795 = _source128.dtor_result;
          DAST._IType _source154 = _3218___mcc_h1;
          if (_source154.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3667___mcc_h802 = _source154.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3668___mcc_h803 = _source154.dtor_typeArgs;
            DAST._IResolvedType _3669___mcc_h804 = _source154.dtor_resolved;
            DAST._IResolvedType _source155 = _3669___mcc_h804;
            if (_source155.is_Datatype) {
              DAST._IDatatypeType _3670___mcc_h808 = _source155.dtor_datatypeType;
              {
                RAST._IExpr _out872;
                DCOMP._IOwnership _out873;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out874;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out872, out _out873, out _out874);
                r = _out872;
                resultingOwnership = _out873;
                readIdents = _out874;
              }
            } else if (_source155.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3671___mcc_h810 = _source155.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3672___mcc_h811 = _source155.dtor_attributes;
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
              DAST._IType _3673___mcc_h814 = _source155.dtor_baseType;
              DAST._INewtypeRange _3674___mcc_h815 = _source155.dtor_range;
              bool _3675___mcc_h816 = _source155.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3676___mcc_h817 = _source155.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3677_attributes = _3676___mcc_h817;
              bool _3678_erase = _3675___mcc_h816;
              DAST._INewtypeRange _3679_range = _3674___mcc_h815;
              DAST._IType _3680_b = _3673___mcc_h814;
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
          } else if (_source154.is_Nullable) {
            DAST._IType _3681___mcc_h822 = _source154.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out881;
              DCOMP._IOwnership _out882;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out883;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out881, out _out882, out _out883);
              r = _out881;
              resultingOwnership = _out882;
              readIdents = _out883;
            }
          } else if (_source154.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3682___mcc_h824 = _source154.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out884;
              DCOMP._IOwnership _out885;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out886;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out884, out _out885, out _out886);
              r = _out884;
              resultingOwnership = _out885;
              readIdents = _out886;
            }
          } else if (_source154.is_Array) {
            DAST._IType _3683___mcc_h826 = _source154.dtor_element;
            BigInteger _3684___mcc_h827 = _source154.dtor_dims;
            {
              RAST._IExpr _out887;
              DCOMP._IOwnership _out888;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out889;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out887, out _out888, out _out889);
              r = _out887;
              resultingOwnership = _out888;
              readIdents = _out889;
            }
          } else if (_source154.is_Seq) {
            DAST._IType _3685___mcc_h830 = _source154.dtor_element;
            {
              RAST._IExpr _out890;
              DCOMP._IOwnership _out891;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out892;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out890, out _out891, out _out892);
              r = _out890;
              resultingOwnership = _out891;
              readIdents = _out892;
            }
          } else if (_source154.is_Set) {
            DAST._IType _3686___mcc_h832 = _source154.dtor_element;
            {
              RAST._IExpr _out893;
              DCOMP._IOwnership _out894;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out895;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out893, out _out894, out _out895);
              r = _out893;
              resultingOwnership = _out894;
              readIdents = _out895;
            }
          } else if (_source154.is_Multiset) {
            DAST._IType _3687___mcc_h834 = _source154.dtor_element;
            {
              RAST._IExpr _out896;
              DCOMP._IOwnership _out897;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out898;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out896, out _out897, out _out898);
              r = _out896;
              resultingOwnership = _out897;
              readIdents = _out898;
            }
          } else if (_source154.is_Map) {
            DAST._IType _3688___mcc_h836 = _source154.dtor_key;
            DAST._IType _3689___mcc_h837 = _source154.dtor_value;
            {
              RAST._IExpr _out899;
              DCOMP._IOwnership _out900;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out901;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out899, out _out900, out _out901);
              r = _out899;
              resultingOwnership = _out900;
              readIdents = _out901;
            }
          } else if (_source154.is_SetBuilder) {
            DAST._IType _3690___mcc_h840 = _source154.dtor_element;
            {
              RAST._IExpr _out902;
              DCOMP._IOwnership _out903;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out904;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out902, out _out903, out _out904);
              r = _out902;
              resultingOwnership = _out903;
              readIdents = _out904;
            }
          } else if (_source154.is_MapBuilder) {
            DAST._IType _3691___mcc_h842 = _source154.dtor_key;
            DAST._IType _3692___mcc_h843 = _source154.dtor_value;
            {
              RAST._IExpr _out905;
              DCOMP._IOwnership _out906;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out907;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out905, out _out906, out _out907);
              r = _out905;
              resultingOwnership = _out906;
              readIdents = _out907;
            }
          } else if (_source154.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3693___mcc_h846 = _source154.dtor_args;
            DAST._IType _3694___mcc_h847 = _source154.dtor_result;
            {
              RAST._IExpr _out908;
              DCOMP._IOwnership _out909;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out910;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out908, out _out909, out _out910);
              r = _out908;
              resultingOwnership = _out909;
              readIdents = _out910;
            }
          } else if (_source154.is_Primitive) {
            DAST._IPrimitive _3695___mcc_h850 = _source154.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out911;
              DCOMP._IOwnership _out912;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out913;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out911, out _out912, out _out913);
              r = _out911;
              resultingOwnership = _out912;
              readIdents = _out913;
            }
          } else if (_source154.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3696___mcc_h852 = _source154.dtor_Passthrough_i_a0;
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
            Dafny.ISequence<Dafny.Rune> _3697___mcc_h854 = _source154.dtor_TypeArg_i_a0;
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
        } else if (_source128.is_Primitive) {
          DAST._IPrimitive _3698___mcc_h856 = _source128.dtor_Primitive_i_a0;
          DAST._IPrimitive _source156 = _3698___mcc_h856;
          if (_source156.is_Int) {
            DAST._IType _source157 = _3218___mcc_h1;
            if (_source157.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3699___mcc_h860 = _source157.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3700___mcc_h861 = _source157.dtor_typeArgs;
              DAST._IResolvedType _3701___mcc_h862 = _source157.dtor_resolved;
              DAST._IResolvedType _source158 = _3701___mcc_h862;
              if (_source158.is_Datatype) {
                DAST._IDatatypeType _3702___mcc_h866 = _source158.dtor_datatypeType;
                {
                  RAST._IExpr _out920;
                  DCOMP._IOwnership _out921;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out922;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out920, out _out921, out _out922);
                  r = _out920;
                  resultingOwnership = _out921;
                  readIdents = _out922;
                }
              } else if (_source158.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3703___mcc_h868 = _source158.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3704___mcc_h869 = _source158.dtor_attributes;
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
                DAST._IType _3705___mcc_h872 = _source158.dtor_baseType;
                DAST._INewtypeRange _3706___mcc_h873 = _source158.dtor_range;
                bool _3707___mcc_h874 = _source158.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3708___mcc_h875 = _source158.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3709_attributes = _3708___mcc_h875;
                bool _3710_erase = _3707___mcc_h874;
                DAST._INewtypeRange _3711_range = _3706___mcc_h873;
                DAST._IType _3712_b = _3705___mcc_h872;
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
            } else if (_source157.is_Nullable) {
              DAST._IType _3713___mcc_h880 = _source157.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out929;
                DCOMP._IOwnership _out930;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out931;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out929, out _out930, out _out931);
                r = _out929;
                resultingOwnership = _out930;
                readIdents = _out931;
              }
            } else if (_source157.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3714___mcc_h882 = _source157.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out932;
                DCOMP._IOwnership _out933;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out934;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out932, out _out933, out _out934);
                r = _out932;
                resultingOwnership = _out933;
                readIdents = _out934;
              }
            } else if (_source157.is_Array) {
              DAST._IType _3715___mcc_h884 = _source157.dtor_element;
              BigInteger _3716___mcc_h885 = _source157.dtor_dims;
              {
                RAST._IExpr _out935;
                DCOMP._IOwnership _out936;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out937;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out935, out _out936, out _out937);
                r = _out935;
                resultingOwnership = _out936;
                readIdents = _out937;
              }
            } else if (_source157.is_Seq) {
              DAST._IType _3717___mcc_h888 = _source157.dtor_element;
              {
                RAST._IExpr _out938;
                DCOMP._IOwnership _out939;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out940;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out938, out _out939, out _out940);
                r = _out938;
                resultingOwnership = _out939;
                readIdents = _out940;
              }
            } else if (_source157.is_Set) {
              DAST._IType _3718___mcc_h890 = _source157.dtor_element;
              {
                RAST._IExpr _out941;
                DCOMP._IOwnership _out942;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out943;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out941, out _out942, out _out943);
                r = _out941;
                resultingOwnership = _out942;
                readIdents = _out943;
              }
            } else if (_source157.is_Multiset) {
              DAST._IType _3719___mcc_h892 = _source157.dtor_element;
              {
                RAST._IExpr _out944;
                DCOMP._IOwnership _out945;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out946;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out944, out _out945, out _out946);
                r = _out944;
                resultingOwnership = _out945;
                readIdents = _out946;
              }
            } else if (_source157.is_Map) {
              DAST._IType _3720___mcc_h894 = _source157.dtor_key;
              DAST._IType _3721___mcc_h895 = _source157.dtor_value;
              {
                RAST._IExpr _out947;
                DCOMP._IOwnership _out948;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out949;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out947, out _out948, out _out949);
                r = _out947;
                resultingOwnership = _out948;
                readIdents = _out949;
              }
            } else if (_source157.is_SetBuilder) {
              DAST._IType _3722___mcc_h898 = _source157.dtor_element;
              {
                RAST._IExpr _out950;
                DCOMP._IOwnership _out951;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out952;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out950, out _out951, out _out952);
                r = _out950;
                resultingOwnership = _out951;
                readIdents = _out952;
              }
            } else if (_source157.is_MapBuilder) {
              DAST._IType _3723___mcc_h900 = _source157.dtor_key;
              DAST._IType _3724___mcc_h901 = _source157.dtor_value;
              {
                RAST._IExpr _out953;
                DCOMP._IOwnership _out954;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out955;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out953, out _out954, out _out955);
                r = _out953;
                resultingOwnership = _out954;
                readIdents = _out955;
              }
            } else if (_source157.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3725___mcc_h904 = _source157.dtor_args;
              DAST._IType _3726___mcc_h905 = _source157.dtor_result;
              {
                RAST._IExpr _out956;
                DCOMP._IOwnership _out957;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out958;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out956, out _out957, out _out958);
                r = _out956;
                resultingOwnership = _out957;
                readIdents = _out958;
              }
            } else if (_source157.is_Primitive) {
              DAST._IPrimitive _3727___mcc_h908 = _source157.dtor_Primitive_i_a0;
              DAST._IPrimitive _source159 = _3727___mcc_h908;
              if (_source159.is_Int) {
                {
                  RAST._IExpr _out959;
                  DCOMP._IOwnership _out960;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out961;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out959, out _out960, out _out961);
                  r = _out959;
                  resultingOwnership = _out960;
                  readIdents = _out961;
                }
              } else if (_source159.is_Real) {
                {
                  RAST._IExpr _3728_recursiveGen;
                  DCOMP._IOwnership _3729___v98;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3730_recIdents;
                  RAST._IExpr _out962;
                  DCOMP._IOwnership _out963;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out964;
                  (this).GenExpr(_3211_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out962, out _out963, out _out964);
                  _3728_recursiveGen = _out962;
                  _3729___v98 = _out963;
                  _3730_recIdents = _out964;
                  r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_3728_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                  RAST._IExpr _out965;
                  DCOMP._IOwnership _out966;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out965, out _out966);
                  r = _out965;
                  resultingOwnership = _out966;
                  readIdents = _3730_recIdents;
                }
              } else if (_source159.is_String) {
                {
                  RAST._IExpr _out967;
                  DCOMP._IOwnership _out968;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out969;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out967, out _out968, out _out969);
                  r = _out967;
                  resultingOwnership = _out968;
                  readIdents = _out969;
                }
              } else if (_source159.is_Bool) {
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
                  RAST._IType _3731_rhsType;
                  RAST._IType _out973;
                  _out973 = (this).GenType(_3213_toTpe, true, false);
                  _3731_rhsType = _out973;
                  RAST._IExpr _3732_recursiveGen;
                  DCOMP._IOwnership _3733___v104;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3734_recIdents;
                  RAST._IExpr _out974;
                  DCOMP._IOwnership _out975;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out976;
                  (this).GenExpr(_3211_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out974, out _out975, out _out976);
                  _3732_recursiveGen = _out974;
                  _3733___v104 = _out975;
                  _3734_recIdents = _out976;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), (_3732_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()")));
                  RAST._IExpr _out977;
                  DCOMP._IOwnership _out978;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out977, out _out978);
                  r = _out977;
                  resultingOwnership = _out978;
                  readIdents = _3734_recIdents;
                }
              }
            } else if (_source157.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3735___mcc_h910 = _source157.dtor_Passthrough_i_a0;
              {
                RAST._IType _3736_rhsType;
                RAST._IType _out979;
                _out979 = (this).GenType(_3213_toTpe, true, false);
                _3736_rhsType = _out979;
                RAST._IExpr _3737_recursiveGen;
                DCOMP._IOwnership _3738___v101;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3739_recIdents;
                RAST._IExpr _out980;
                DCOMP._IOwnership _out981;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out982;
                (this).GenExpr(_3211_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out980, out _out981, out _out982);
                _3737_recursiveGen = _out980;
                _3738___v101 = _out981;
                _3739_recIdents = _out982;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_3736_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_3737_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                RAST._IExpr _out983;
                DCOMP._IOwnership _out984;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out983, out _out984);
                r = _out983;
                resultingOwnership = _out984;
                readIdents = _3739_recIdents;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3740___mcc_h912 = _source157.dtor_TypeArg_i_a0;
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
          } else if (_source156.is_Real) {
            DAST._IType _source160 = _3218___mcc_h1;
            if (_source160.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3741___mcc_h914 = _source160.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3742___mcc_h915 = _source160.dtor_typeArgs;
              DAST._IResolvedType _3743___mcc_h916 = _source160.dtor_resolved;
              DAST._IResolvedType _source161 = _3743___mcc_h916;
              if (_source161.is_Datatype) {
                DAST._IDatatypeType _3744___mcc_h920 = _source161.dtor_datatypeType;
                {
                  RAST._IExpr _out988;
                  DCOMP._IOwnership _out989;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out990;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out988, out _out989, out _out990);
                  r = _out988;
                  resultingOwnership = _out989;
                  readIdents = _out990;
                }
              } else if (_source161.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3745___mcc_h922 = _source161.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3746___mcc_h923 = _source161.dtor_attributes;
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
                DAST._IType _3747___mcc_h926 = _source161.dtor_baseType;
                DAST._INewtypeRange _3748___mcc_h927 = _source161.dtor_range;
                bool _3749___mcc_h928 = _source161.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3750___mcc_h929 = _source161.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3751_attributes = _3750___mcc_h929;
                bool _3752_erase = _3749___mcc_h928;
                DAST._INewtypeRange _3753_range = _3748___mcc_h927;
                DAST._IType _3754_b = _3747___mcc_h926;
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
            } else if (_source160.is_Nullable) {
              DAST._IType _3755___mcc_h934 = _source160.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out997;
                DCOMP._IOwnership _out998;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out999;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out997, out _out998, out _out999);
                r = _out997;
                resultingOwnership = _out998;
                readIdents = _out999;
              }
            } else if (_source160.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3756___mcc_h936 = _source160.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out1000;
                DCOMP._IOwnership _out1001;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1002;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1000, out _out1001, out _out1002);
                r = _out1000;
                resultingOwnership = _out1001;
                readIdents = _out1002;
              }
            } else if (_source160.is_Array) {
              DAST._IType _3757___mcc_h938 = _source160.dtor_element;
              BigInteger _3758___mcc_h939 = _source160.dtor_dims;
              {
                RAST._IExpr _out1003;
                DCOMP._IOwnership _out1004;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1005;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1003, out _out1004, out _out1005);
                r = _out1003;
                resultingOwnership = _out1004;
                readIdents = _out1005;
              }
            } else if (_source160.is_Seq) {
              DAST._IType _3759___mcc_h942 = _source160.dtor_element;
              {
                RAST._IExpr _out1006;
                DCOMP._IOwnership _out1007;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1008;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1006, out _out1007, out _out1008);
                r = _out1006;
                resultingOwnership = _out1007;
                readIdents = _out1008;
              }
            } else if (_source160.is_Set) {
              DAST._IType _3760___mcc_h944 = _source160.dtor_element;
              {
                RAST._IExpr _out1009;
                DCOMP._IOwnership _out1010;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1011;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1009, out _out1010, out _out1011);
                r = _out1009;
                resultingOwnership = _out1010;
                readIdents = _out1011;
              }
            } else if (_source160.is_Multiset) {
              DAST._IType _3761___mcc_h946 = _source160.dtor_element;
              {
                RAST._IExpr _out1012;
                DCOMP._IOwnership _out1013;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1014;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1012, out _out1013, out _out1014);
                r = _out1012;
                resultingOwnership = _out1013;
                readIdents = _out1014;
              }
            } else if (_source160.is_Map) {
              DAST._IType _3762___mcc_h948 = _source160.dtor_key;
              DAST._IType _3763___mcc_h949 = _source160.dtor_value;
              {
                RAST._IExpr _out1015;
                DCOMP._IOwnership _out1016;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1017;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1015, out _out1016, out _out1017);
                r = _out1015;
                resultingOwnership = _out1016;
                readIdents = _out1017;
              }
            } else if (_source160.is_SetBuilder) {
              DAST._IType _3764___mcc_h952 = _source160.dtor_element;
              {
                RAST._IExpr _out1018;
                DCOMP._IOwnership _out1019;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1020;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1018, out _out1019, out _out1020);
                r = _out1018;
                resultingOwnership = _out1019;
                readIdents = _out1020;
              }
            } else if (_source160.is_MapBuilder) {
              DAST._IType _3765___mcc_h954 = _source160.dtor_key;
              DAST._IType _3766___mcc_h955 = _source160.dtor_value;
              {
                RAST._IExpr _out1021;
                DCOMP._IOwnership _out1022;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1023;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1021, out _out1022, out _out1023);
                r = _out1021;
                resultingOwnership = _out1022;
                readIdents = _out1023;
              }
            } else if (_source160.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3767___mcc_h958 = _source160.dtor_args;
              DAST._IType _3768___mcc_h959 = _source160.dtor_result;
              {
                RAST._IExpr _out1024;
                DCOMP._IOwnership _out1025;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1026;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1024, out _out1025, out _out1026);
                r = _out1024;
                resultingOwnership = _out1025;
                readIdents = _out1026;
              }
            } else if (_source160.is_Primitive) {
              DAST._IPrimitive _3769___mcc_h962 = _source160.dtor_Primitive_i_a0;
              DAST._IPrimitive _source162 = _3769___mcc_h962;
              if (_source162.is_Int) {
                {
                  RAST._IExpr _3770_recursiveGen;
                  DCOMP._IOwnership _3771___v99;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3772_recIdents;
                  RAST._IExpr _out1027;
                  DCOMP._IOwnership _out1028;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1029;
                  (this).GenExpr(_3211_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1027, out _out1028, out _out1029);
                  _3770_recursiveGen = _out1027;
                  _3771___v99 = _out1028;
                  _3772_recIdents = _out1029;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_3770_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                  RAST._IExpr _out1030;
                  DCOMP._IOwnership _out1031;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1030, out _out1031);
                  r = _out1030;
                  resultingOwnership = _out1031;
                  readIdents = _3772_recIdents;
                }
              } else if (_source162.is_Real) {
                {
                  RAST._IExpr _out1032;
                  DCOMP._IOwnership _out1033;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1034;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1032, out _out1033, out _out1034);
                  r = _out1032;
                  resultingOwnership = _out1033;
                  readIdents = _out1034;
                }
              } else if (_source162.is_String) {
                {
                  RAST._IExpr _out1035;
                  DCOMP._IOwnership _out1036;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1037;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1035, out _out1036, out _out1037);
                  r = _out1035;
                  resultingOwnership = _out1036;
                  readIdents = _out1037;
                }
              } else if (_source162.is_Bool) {
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
            } else if (_source160.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3773___mcc_h964 = _source160.dtor_Passthrough_i_a0;
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
              Dafny.ISequence<Dafny.Rune> _3774___mcc_h966 = _source160.dtor_TypeArg_i_a0;
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
          } else if (_source156.is_String) {
            DAST._IType _source163 = _3218___mcc_h1;
            if (_source163.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3775___mcc_h968 = _source163.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3776___mcc_h969 = _source163.dtor_typeArgs;
              DAST._IResolvedType _3777___mcc_h970 = _source163.dtor_resolved;
              DAST._IResolvedType _source164 = _3777___mcc_h970;
              if (_source164.is_Datatype) {
                DAST._IDatatypeType _3778___mcc_h974 = _source164.dtor_datatypeType;
                {
                  RAST._IExpr _out1050;
                  DCOMP._IOwnership _out1051;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1052;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1050, out _out1051, out _out1052);
                  r = _out1050;
                  resultingOwnership = _out1051;
                  readIdents = _out1052;
                }
              } else if (_source164.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3779___mcc_h976 = _source164.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3780___mcc_h977 = _source164.dtor_attributes;
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
                DAST._IType _3781___mcc_h980 = _source164.dtor_baseType;
                DAST._INewtypeRange _3782___mcc_h981 = _source164.dtor_range;
                bool _3783___mcc_h982 = _source164.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3784___mcc_h983 = _source164.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3785_attributes = _3784___mcc_h983;
                bool _3786_erase = _3783___mcc_h982;
                DAST._INewtypeRange _3787_range = _3782___mcc_h981;
                DAST._IType _3788_b = _3781___mcc_h980;
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
            } else if (_source163.is_Nullable) {
              DAST._IType _3789___mcc_h988 = _source163.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out1059;
                DCOMP._IOwnership _out1060;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1061;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1059, out _out1060, out _out1061);
                r = _out1059;
                resultingOwnership = _out1060;
                readIdents = _out1061;
              }
            } else if (_source163.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3790___mcc_h990 = _source163.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out1062;
                DCOMP._IOwnership _out1063;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1064;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1062, out _out1063, out _out1064);
                r = _out1062;
                resultingOwnership = _out1063;
                readIdents = _out1064;
              }
            } else if (_source163.is_Array) {
              DAST._IType _3791___mcc_h992 = _source163.dtor_element;
              BigInteger _3792___mcc_h993 = _source163.dtor_dims;
              {
                RAST._IExpr _out1065;
                DCOMP._IOwnership _out1066;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1067;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1065, out _out1066, out _out1067);
                r = _out1065;
                resultingOwnership = _out1066;
                readIdents = _out1067;
              }
            } else if (_source163.is_Seq) {
              DAST._IType _3793___mcc_h996 = _source163.dtor_element;
              {
                RAST._IExpr _out1068;
                DCOMP._IOwnership _out1069;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1070;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1068, out _out1069, out _out1070);
                r = _out1068;
                resultingOwnership = _out1069;
                readIdents = _out1070;
              }
            } else if (_source163.is_Set) {
              DAST._IType _3794___mcc_h998 = _source163.dtor_element;
              {
                RAST._IExpr _out1071;
                DCOMP._IOwnership _out1072;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1073;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1071, out _out1072, out _out1073);
                r = _out1071;
                resultingOwnership = _out1072;
                readIdents = _out1073;
              }
            } else if (_source163.is_Multiset) {
              DAST._IType _3795___mcc_h1000 = _source163.dtor_element;
              {
                RAST._IExpr _out1074;
                DCOMP._IOwnership _out1075;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1076;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1074, out _out1075, out _out1076);
                r = _out1074;
                resultingOwnership = _out1075;
                readIdents = _out1076;
              }
            } else if (_source163.is_Map) {
              DAST._IType _3796___mcc_h1002 = _source163.dtor_key;
              DAST._IType _3797___mcc_h1003 = _source163.dtor_value;
              {
                RAST._IExpr _out1077;
                DCOMP._IOwnership _out1078;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1079;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1077, out _out1078, out _out1079);
                r = _out1077;
                resultingOwnership = _out1078;
                readIdents = _out1079;
              }
            } else if (_source163.is_SetBuilder) {
              DAST._IType _3798___mcc_h1006 = _source163.dtor_element;
              {
                RAST._IExpr _out1080;
                DCOMP._IOwnership _out1081;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1082;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1080, out _out1081, out _out1082);
                r = _out1080;
                resultingOwnership = _out1081;
                readIdents = _out1082;
              }
            } else if (_source163.is_MapBuilder) {
              DAST._IType _3799___mcc_h1008 = _source163.dtor_key;
              DAST._IType _3800___mcc_h1009 = _source163.dtor_value;
              {
                RAST._IExpr _out1083;
                DCOMP._IOwnership _out1084;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1085;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1083, out _out1084, out _out1085);
                r = _out1083;
                resultingOwnership = _out1084;
                readIdents = _out1085;
              }
            } else if (_source163.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3801___mcc_h1012 = _source163.dtor_args;
              DAST._IType _3802___mcc_h1013 = _source163.dtor_result;
              {
                RAST._IExpr _out1086;
                DCOMP._IOwnership _out1087;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1088;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1086, out _out1087, out _out1088);
                r = _out1086;
                resultingOwnership = _out1087;
                readIdents = _out1088;
              }
            } else if (_source163.is_Primitive) {
              DAST._IPrimitive _3803___mcc_h1016 = _source163.dtor_Primitive_i_a0;
              {
                RAST._IExpr _out1089;
                DCOMP._IOwnership _out1090;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1091;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1089, out _out1090, out _out1091);
                r = _out1089;
                resultingOwnership = _out1090;
                readIdents = _out1091;
              }
            } else if (_source163.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3804___mcc_h1018 = _source163.dtor_Passthrough_i_a0;
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
              Dafny.ISequence<Dafny.Rune> _3805___mcc_h1020 = _source163.dtor_TypeArg_i_a0;
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
          } else if (_source156.is_Bool) {
            DAST._IType _source165 = _3218___mcc_h1;
            if (_source165.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3806___mcc_h1022 = _source165.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3807___mcc_h1023 = _source165.dtor_typeArgs;
              DAST._IResolvedType _3808___mcc_h1024 = _source165.dtor_resolved;
              DAST._IResolvedType _source166 = _3808___mcc_h1024;
              if (_source166.is_Datatype) {
                DAST._IDatatypeType _3809___mcc_h1028 = _source166.dtor_datatypeType;
                {
                  RAST._IExpr _out1098;
                  DCOMP._IOwnership _out1099;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1100;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1098, out _out1099, out _out1100);
                  r = _out1098;
                  resultingOwnership = _out1099;
                  readIdents = _out1100;
                }
              } else if (_source166.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3810___mcc_h1030 = _source166.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3811___mcc_h1031 = _source166.dtor_attributes;
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
                DAST._IType _3812___mcc_h1034 = _source166.dtor_baseType;
                DAST._INewtypeRange _3813___mcc_h1035 = _source166.dtor_range;
                bool _3814___mcc_h1036 = _source166.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3815___mcc_h1037 = _source166.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3816_attributes = _3815___mcc_h1037;
                bool _3817_erase = _3814___mcc_h1036;
                DAST._INewtypeRange _3818_range = _3813___mcc_h1035;
                DAST._IType _3819_b = _3812___mcc_h1034;
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
            } else if (_source165.is_Nullable) {
              DAST._IType _3820___mcc_h1042 = _source165.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out1107;
                DCOMP._IOwnership _out1108;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1109;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1107, out _out1108, out _out1109);
                r = _out1107;
                resultingOwnership = _out1108;
                readIdents = _out1109;
              }
            } else if (_source165.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3821___mcc_h1044 = _source165.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out1110;
                DCOMP._IOwnership _out1111;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1112;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1110, out _out1111, out _out1112);
                r = _out1110;
                resultingOwnership = _out1111;
                readIdents = _out1112;
              }
            } else if (_source165.is_Array) {
              DAST._IType _3822___mcc_h1046 = _source165.dtor_element;
              BigInteger _3823___mcc_h1047 = _source165.dtor_dims;
              {
                RAST._IExpr _out1113;
                DCOMP._IOwnership _out1114;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1115;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1113, out _out1114, out _out1115);
                r = _out1113;
                resultingOwnership = _out1114;
                readIdents = _out1115;
              }
            } else if (_source165.is_Seq) {
              DAST._IType _3824___mcc_h1050 = _source165.dtor_element;
              {
                RAST._IExpr _out1116;
                DCOMP._IOwnership _out1117;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1118;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1116, out _out1117, out _out1118);
                r = _out1116;
                resultingOwnership = _out1117;
                readIdents = _out1118;
              }
            } else if (_source165.is_Set) {
              DAST._IType _3825___mcc_h1052 = _source165.dtor_element;
              {
                RAST._IExpr _out1119;
                DCOMP._IOwnership _out1120;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1121;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1119, out _out1120, out _out1121);
                r = _out1119;
                resultingOwnership = _out1120;
                readIdents = _out1121;
              }
            } else if (_source165.is_Multiset) {
              DAST._IType _3826___mcc_h1054 = _source165.dtor_element;
              {
                RAST._IExpr _out1122;
                DCOMP._IOwnership _out1123;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1124;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1122, out _out1123, out _out1124);
                r = _out1122;
                resultingOwnership = _out1123;
                readIdents = _out1124;
              }
            } else if (_source165.is_Map) {
              DAST._IType _3827___mcc_h1056 = _source165.dtor_key;
              DAST._IType _3828___mcc_h1057 = _source165.dtor_value;
              {
                RAST._IExpr _out1125;
                DCOMP._IOwnership _out1126;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1127;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1125, out _out1126, out _out1127);
                r = _out1125;
                resultingOwnership = _out1126;
                readIdents = _out1127;
              }
            } else if (_source165.is_SetBuilder) {
              DAST._IType _3829___mcc_h1060 = _source165.dtor_element;
              {
                RAST._IExpr _out1128;
                DCOMP._IOwnership _out1129;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1130;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1128, out _out1129, out _out1130);
                r = _out1128;
                resultingOwnership = _out1129;
                readIdents = _out1130;
              }
            } else if (_source165.is_MapBuilder) {
              DAST._IType _3830___mcc_h1062 = _source165.dtor_key;
              DAST._IType _3831___mcc_h1063 = _source165.dtor_value;
              {
                RAST._IExpr _out1131;
                DCOMP._IOwnership _out1132;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1133;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1131, out _out1132, out _out1133);
                r = _out1131;
                resultingOwnership = _out1132;
                readIdents = _out1133;
              }
            } else if (_source165.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3832___mcc_h1066 = _source165.dtor_args;
              DAST._IType _3833___mcc_h1067 = _source165.dtor_result;
              {
                RAST._IExpr _out1134;
                DCOMP._IOwnership _out1135;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1136;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1134, out _out1135, out _out1136);
                r = _out1134;
                resultingOwnership = _out1135;
                readIdents = _out1136;
              }
            } else if (_source165.is_Primitive) {
              DAST._IPrimitive _3834___mcc_h1070 = _source165.dtor_Primitive_i_a0;
              {
                RAST._IExpr _out1137;
                DCOMP._IOwnership _out1138;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1139;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1137, out _out1138, out _out1139);
                r = _out1137;
                resultingOwnership = _out1138;
                readIdents = _out1139;
              }
            } else if (_source165.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3835___mcc_h1072 = _source165.dtor_Passthrough_i_a0;
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
              Dafny.ISequence<Dafny.Rune> _3836___mcc_h1074 = _source165.dtor_TypeArg_i_a0;
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
            DAST._IType _source167 = _3218___mcc_h1;
            if (_source167.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3837___mcc_h1076 = _source167.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3838___mcc_h1077 = _source167.dtor_typeArgs;
              DAST._IResolvedType _3839___mcc_h1078 = _source167.dtor_resolved;
              DAST._IResolvedType _source168 = _3839___mcc_h1078;
              if (_source168.is_Datatype) {
                DAST._IDatatypeType _3840___mcc_h1082 = _source168.dtor_datatypeType;
                {
                  RAST._IExpr _out1146;
                  DCOMP._IOwnership _out1147;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1148;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1146, out _out1147, out _out1148);
                  r = _out1146;
                  resultingOwnership = _out1147;
                  readIdents = _out1148;
                }
              } else if (_source168.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3841___mcc_h1084 = _source168.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3842___mcc_h1085 = _source168.dtor_attributes;
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
                DAST._IType _3843___mcc_h1088 = _source168.dtor_baseType;
                DAST._INewtypeRange _3844___mcc_h1089 = _source168.dtor_range;
                bool _3845___mcc_h1090 = _source168.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3846___mcc_h1091 = _source168.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3847_attributes = _3846___mcc_h1091;
                bool _3848_erase = _3845___mcc_h1090;
                DAST._INewtypeRange _3849_range = _3844___mcc_h1089;
                DAST._IType _3850_b = _3843___mcc_h1088;
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
            } else if (_source167.is_Nullable) {
              DAST._IType _3851___mcc_h1096 = _source167.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out1155;
                DCOMP._IOwnership _out1156;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1157;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1155, out _out1156, out _out1157);
                r = _out1155;
                resultingOwnership = _out1156;
                readIdents = _out1157;
              }
            } else if (_source167.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3852___mcc_h1098 = _source167.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out1158;
                DCOMP._IOwnership _out1159;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1160;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1158, out _out1159, out _out1160);
                r = _out1158;
                resultingOwnership = _out1159;
                readIdents = _out1160;
              }
            } else if (_source167.is_Array) {
              DAST._IType _3853___mcc_h1100 = _source167.dtor_element;
              BigInteger _3854___mcc_h1101 = _source167.dtor_dims;
              {
                RAST._IExpr _out1161;
                DCOMP._IOwnership _out1162;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1163;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1161, out _out1162, out _out1163);
                r = _out1161;
                resultingOwnership = _out1162;
                readIdents = _out1163;
              }
            } else if (_source167.is_Seq) {
              DAST._IType _3855___mcc_h1104 = _source167.dtor_element;
              {
                RAST._IExpr _out1164;
                DCOMP._IOwnership _out1165;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1166;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1164, out _out1165, out _out1166);
                r = _out1164;
                resultingOwnership = _out1165;
                readIdents = _out1166;
              }
            } else if (_source167.is_Set) {
              DAST._IType _3856___mcc_h1106 = _source167.dtor_element;
              {
                RAST._IExpr _out1167;
                DCOMP._IOwnership _out1168;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1169;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1167, out _out1168, out _out1169);
                r = _out1167;
                resultingOwnership = _out1168;
                readIdents = _out1169;
              }
            } else if (_source167.is_Multiset) {
              DAST._IType _3857___mcc_h1108 = _source167.dtor_element;
              {
                RAST._IExpr _out1170;
                DCOMP._IOwnership _out1171;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1172;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1170, out _out1171, out _out1172);
                r = _out1170;
                resultingOwnership = _out1171;
                readIdents = _out1172;
              }
            } else if (_source167.is_Map) {
              DAST._IType _3858___mcc_h1110 = _source167.dtor_key;
              DAST._IType _3859___mcc_h1111 = _source167.dtor_value;
              {
                RAST._IExpr _out1173;
                DCOMP._IOwnership _out1174;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1175;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1173, out _out1174, out _out1175);
                r = _out1173;
                resultingOwnership = _out1174;
                readIdents = _out1175;
              }
            } else if (_source167.is_SetBuilder) {
              DAST._IType _3860___mcc_h1114 = _source167.dtor_element;
              {
                RAST._IExpr _out1176;
                DCOMP._IOwnership _out1177;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1178;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1176, out _out1177, out _out1178);
                r = _out1176;
                resultingOwnership = _out1177;
                readIdents = _out1178;
              }
            } else if (_source167.is_MapBuilder) {
              DAST._IType _3861___mcc_h1116 = _source167.dtor_key;
              DAST._IType _3862___mcc_h1117 = _source167.dtor_value;
              {
                RAST._IExpr _out1179;
                DCOMP._IOwnership _out1180;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1181;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1179, out _out1180, out _out1181);
                r = _out1179;
                resultingOwnership = _out1180;
                readIdents = _out1181;
              }
            } else if (_source167.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3863___mcc_h1120 = _source167.dtor_args;
              DAST._IType _3864___mcc_h1121 = _source167.dtor_result;
              {
                RAST._IExpr _out1182;
                DCOMP._IOwnership _out1183;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1184;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1182, out _out1183, out _out1184);
                r = _out1182;
                resultingOwnership = _out1183;
                readIdents = _out1184;
              }
            } else if (_source167.is_Primitive) {
              DAST._IPrimitive _3865___mcc_h1124 = _source167.dtor_Primitive_i_a0;
              DAST._IPrimitive _source169 = _3865___mcc_h1124;
              if (_source169.is_Int) {
                {
                  RAST._IType _3866_rhsType;
                  RAST._IType _out1185;
                  _out1185 = (this).GenType(_3212_fromTpe, true, false);
                  _3866_rhsType = _out1185;
                  RAST._IExpr _3867_recursiveGen;
                  DCOMP._IOwnership _3868___v105;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3869_recIdents;
                  RAST._IExpr _out1186;
                  DCOMP._IOwnership _out1187;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1188;
                  (this).GenExpr(_3211_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1186, out _out1187, out _out1188);
                  _3867_recursiveGen = _out1186;
                  _3868___v105 = _out1187;
                  _3869_recIdents = _out1188;
                  r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_3867_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                  RAST._IExpr _out1189;
                  DCOMP._IOwnership _out1190;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1189, out _out1190);
                  r = _out1189;
                  resultingOwnership = _out1190;
                  readIdents = _3869_recIdents;
                }
              } else if (_source169.is_Real) {
                {
                  RAST._IExpr _out1191;
                  DCOMP._IOwnership _out1192;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1193;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1191, out _out1192, out _out1193);
                  r = _out1191;
                  resultingOwnership = _out1192;
                  readIdents = _out1193;
                }
              } else if (_source169.is_String) {
                {
                  RAST._IExpr _out1194;
                  DCOMP._IOwnership _out1195;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1196;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1194, out _out1195, out _out1196);
                  r = _out1194;
                  resultingOwnership = _out1195;
                  readIdents = _out1196;
                }
              } else if (_source169.is_Bool) {
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
            } else if (_source167.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3870___mcc_h1126 = _source167.dtor_Passthrough_i_a0;
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
              Dafny.ISequence<Dafny.Rune> _3871___mcc_h1128 = _source167.dtor_TypeArg_i_a0;
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
        } else if (_source128.is_Passthrough) {
          Dafny.ISequence<Dafny.Rune> _3872___mcc_h1130 = _source128.dtor_Passthrough_i_a0;
          DAST._IType _source170 = _3218___mcc_h1;
          if (_source170.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3873___mcc_h1134 = _source170.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3874___mcc_h1135 = _source170.dtor_typeArgs;
            DAST._IResolvedType _3875___mcc_h1136 = _source170.dtor_resolved;
            DAST._IResolvedType _source171 = _3875___mcc_h1136;
            if (_source171.is_Datatype) {
              DAST._IDatatypeType _3876___mcc_h1140 = _source171.dtor_datatypeType;
              {
                RAST._IExpr _out1209;
                DCOMP._IOwnership _out1210;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1211;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1209, out _out1210, out _out1211);
                r = _out1209;
                resultingOwnership = _out1210;
                readIdents = _out1211;
              }
            } else if (_source171.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3877___mcc_h1142 = _source171.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3878___mcc_h1143 = _source171.dtor_attributes;
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
              DAST._IType _3879___mcc_h1146 = _source171.dtor_baseType;
              DAST._INewtypeRange _3880___mcc_h1147 = _source171.dtor_range;
              bool _3881___mcc_h1148 = _source171.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3882___mcc_h1149 = _source171.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3883_attributes = _3882___mcc_h1149;
              bool _3884_erase = _3881___mcc_h1148;
              DAST._INewtypeRange _3885_range = _3880___mcc_h1147;
              DAST._IType _3886_b = _3879___mcc_h1146;
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
          } else if (_source170.is_Nullable) {
            DAST._IType _3887___mcc_h1154 = _source170.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out1218;
              DCOMP._IOwnership _out1219;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1220;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1218, out _out1219, out _out1220);
              r = _out1218;
              resultingOwnership = _out1219;
              readIdents = _out1220;
            }
          } else if (_source170.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3888___mcc_h1156 = _source170.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out1221;
              DCOMP._IOwnership _out1222;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1223;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1221, out _out1222, out _out1223);
              r = _out1221;
              resultingOwnership = _out1222;
              readIdents = _out1223;
            }
          } else if (_source170.is_Array) {
            DAST._IType _3889___mcc_h1158 = _source170.dtor_element;
            BigInteger _3890___mcc_h1159 = _source170.dtor_dims;
            {
              RAST._IExpr _out1224;
              DCOMP._IOwnership _out1225;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1226;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1224, out _out1225, out _out1226);
              r = _out1224;
              resultingOwnership = _out1225;
              readIdents = _out1226;
            }
          } else if (_source170.is_Seq) {
            DAST._IType _3891___mcc_h1162 = _source170.dtor_element;
            {
              RAST._IExpr _out1227;
              DCOMP._IOwnership _out1228;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1229;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1227, out _out1228, out _out1229);
              r = _out1227;
              resultingOwnership = _out1228;
              readIdents = _out1229;
            }
          } else if (_source170.is_Set) {
            DAST._IType _3892___mcc_h1164 = _source170.dtor_element;
            {
              RAST._IExpr _out1230;
              DCOMP._IOwnership _out1231;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1232;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1230, out _out1231, out _out1232);
              r = _out1230;
              resultingOwnership = _out1231;
              readIdents = _out1232;
            }
          } else if (_source170.is_Multiset) {
            DAST._IType _3893___mcc_h1166 = _source170.dtor_element;
            {
              RAST._IExpr _out1233;
              DCOMP._IOwnership _out1234;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1235;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1233, out _out1234, out _out1235);
              r = _out1233;
              resultingOwnership = _out1234;
              readIdents = _out1235;
            }
          } else if (_source170.is_Map) {
            DAST._IType _3894___mcc_h1168 = _source170.dtor_key;
            DAST._IType _3895___mcc_h1169 = _source170.dtor_value;
            {
              RAST._IExpr _out1236;
              DCOMP._IOwnership _out1237;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1238;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1236, out _out1237, out _out1238);
              r = _out1236;
              resultingOwnership = _out1237;
              readIdents = _out1238;
            }
          } else if (_source170.is_SetBuilder) {
            DAST._IType _3896___mcc_h1172 = _source170.dtor_element;
            {
              RAST._IExpr _out1239;
              DCOMP._IOwnership _out1240;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1241;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1239, out _out1240, out _out1241);
              r = _out1239;
              resultingOwnership = _out1240;
              readIdents = _out1241;
            }
          } else if (_source170.is_MapBuilder) {
            DAST._IType _3897___mcc_h1174 = _source170.dtor_key;
            DAST._IType _3898___mcc_h1175 = _source170.dtor_value;
            {
              RAST._IExpr _out1242;
              DCOMP._IOwnership _out1243;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1244;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1242, out _out1243, out _out1244);
              r = _out1242;
              resultingOwnership = _out1243;
              readIdents = _out1244;
            }
          } else if (_source170.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3899___mcc_h1178 = _source170.dtor_args;
            DAST._IType _3900___mcc_h1179 = _source170.dtor_result;
            {
              RAST._IExpr _out1245;
              DCOMP._IOwnership _out1246;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1247;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1245, out _out1246, out _out1247);
              r = _out1245;
              resultingOwnership = _out1246;
              readIdents = _out1247;
            }
          } else if (_source170.is_Primitive) {
            DAST._IPrimitive _3901___mcc_h1182 = _source170.dtor_Primitive_i_a0;
            DAST._IPrimitive _source172 = _3901___mcc_h1182;
            if (_source172.is_Int) {
              {
                RAST._IType _3902_rhsType;
                RAST._IType _out1248;
                _out1248 = (this).GenType(_3212_fromTpe, true, false);
                _3902_rhsType = _out1248;
                RAST._IExpr _3903_recursiveGen;
                DCOMP._IOwnership _3904___v103;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3905_recIdents;
                RAST._IExpr _out1249;
                DCOMP._IOwnership _out1250;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1251;
                (this).GenExpr(_3211_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1249, out _out1250, out _out1251);
                _3903_recursiveGen = _out1249;
                _3904___v103 = _out1250;
                _3905_recIdents = _out1251;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::dafny_runtime::BigInt::from("), (_3903_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")}")));
                RAST._IExpr _out1252;
                DCOMP._IOwnership _out1253;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1252, out _out1253);
                r = _out1252;
                resultingOwnership = _out1253;
                readIdents = _3905_recIdents;
              }
            } else if (_source172.is_Real) {
              {
                RAST._IExpr _out1254;
                DCOMP._IOwnership _out1255;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1256;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1254, out _out1255, out _out1256);
                r = _out1254;
                resultingOwnership = _out1255;
                readIdents = _out1256;
              }
            } else if (_source172.is_String) {
              {
                RAST._IExpr _out1257;
                DCOMP._IOwnership _out1258;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1259;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1257, out _out1258, out _out1259);
                r = _out1257;
                resultingOwnership = _out1258;
                readIdents = _out1259;
              }
            } else if (_source172.is_Bool) {
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
          } else if (_source170.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3906___mcc_h1184 = _source170.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _3907_recursiveGen;
              DCOMP._IOwnership _3908___v108;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3909_recIdents;
              RAST._IExpr _out1266;
              DCOMP._IOwnership _out1267;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1268;
              (this).GenExpr(_3211_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1266, out _out1267, out _out1268);
              _3907_recursiveGen = _out1266;
              _3908___v108 = _out1267;
              _3909_recIdents = _out1268;
              RAST._IType _3910_toTpeGen;
              RAST._IType _out1269;
              _out1269 = (this).GenType(_3213_toTpe, true, false);
              _3910_toTpeGen = _out1269;
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_3907_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_3910_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
              RAST._IExpr _out1270;
              DCOMP._IOwnership _out1271;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1270, out _out1271);
              r = _out1270;
              resultingOwnership = _out1271;
              readIdents = _3909_recIdents;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3911___mcc_h1186 = _source170.dtor_TypeArg_i_a0;
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
          Dafny.ISequence<Dafny.Rune> _3912___mcc_h1188 = _source128.dtor_TypeArg_i_a0;
          DAST._IType _source173 = _3218___mcc_h1;
          if (_source173.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3913___mcc_h1192 = _source173.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3914___mcc_h1193 = _source173.dtor_typeArgs;
            DAST._IResolvedType _3915___mcc_h1194 = _source173.dtor_resolved;
            DAST._IResolvedType _source174 = _3915___mcc_h1194;
            if (_source174.is_Datatype) {
              DAST._IDatatypeType _3916___mcc_h1198 = _source174.dtor_datatypeType;
              {
                RAST._IExpr _out1275;
                DCOMP._IOwnership _out1276;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1277;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1275, out _out1276, out _out1277);
                r = _out1275;
                resultingOwnership = _out1276;
                readIdents = _out1277;
              }
            } else if (_source174.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3917___mcc_h1200 = _source174.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3918___mcc_h1201 = _source174.dtor_attributes;
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
              DAST._IType _3919___mcc_h1204 = _source174.dtor_baseType;
              DAST._INewtypeRange _3920___mcc_h1205 = _source174.dtor_range;
              bool _3921___mcc_h1206 = _source174.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3922___mcc_h1207 = _source174.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3923_attributes = _3922___mcc_h1207;
              bool _3924_erase = _3921___mcc_h1206;
              DAST._INewtypeRange _3925_range = _3920___mcc_h1205;
              DAST._IType _3926_b = _3919___mcc_h1204;
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
          } else if (_source173.is_Nullable) {
            DAST._IType _3927___mcc_h1212 = _source173.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out1284;
              DCOMP._IOwnership _out1285;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1286;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1284, out _out1285, out _out1286);
              r = _out1284;
              resultingOwnership = _out1285;
              readIdents = _out1286;
            }
          } else if (_source173.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3928___mcc_h1214 = _source173.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out1287;
              DCOMP._IOwnership _out1288;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1289;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1287, out _out1288, out _out1289);
              r = _out1287;
              resultingOwnership = _out1288;
              readIdents = _out1289;
            }
          } else if (_source173.is_Array) {
            DAST._IType _3929___mcc_h1216 = _source173.dtor_element;
            BigInteger _3930___mcc_h1217 = _source173.dtor_dims;
            {
              RAST._IExpr _out1290;
              DCOMP._IOwnership _out1291;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1292;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1290, out _out1291, out _out1292);
              r = _out1290;
              resultingOwnership = _out1291;
              readIdents = _out1292;
            }
          } else if (_source173.is_Seq) {
            DAST._IType _3931___mcc_h1220 = _source173.dtor_element;
            {
              RAST._IExpr _out1293;
              DCOMP._IOwnership _out1294;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1295;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1293, out _out1294, out _out1295);
              r = _out1293;
              resultingOwnership = _out1294;
              readIdents = _out1295;
            }
          } else if (_source173.is_Set) {
            DAST._IType _3932___mcc_h1222 = _source173.dtor_element;
            {
              RAST._IExpr _out1296;
              DCOMP._IOwnership _out1297;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1298;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1296, out _out1297, out _out1298);
              r = _out1296;
              resultingOwnership = _out1297;
              readIdents = _out1298;
            }
          } else if (_source173.is_Multiset) {
            DAST._IType _3933___mcc_h1224 = _source173.dtor_element;
            {
              RAST._IExpr _out1299;
              DCOMP._IOwnership _out1300;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1301;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1299, out _out1300, out _out1301);
              r = _out1299;
              resultingOwnership = _out1300;
              readIdents = _out1301;
            }
          } else if (_source173.is_Map) {
            DAST._IType _3934___mcc_h1226 = _source173.dtor_key;
            DAST._IType _3935___mcc_h1227 = _source173.dtor_value;
            {
              RAST._IExpr _out1302;
              DCOMP._IOwnership _out1303;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1304;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1302, out _out1303, out _out1304);
              r = _out1302;
              resultingOwnership = _out1303;
              readIdents = _out1304;
            }
          } else if (_source173.is_SetBuilder) {
            DAST._IType _3936___mcc_h1230 = _source173.dtor_element;
            {
              RAST._IExpr _out1305;
              DCOMP._IOwnership _out1306;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1307;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1305, out _out1306, out _out1307);
              r = _out1305;
              resultingOwnership = _out1306;
              readIdents = _out1307;
            }
          } else if (_source173.is_MapBuilder) {
            DAST._IType _3937___mcc_h1232 = _source173.dtor_key;
            DAST._IType _3938___mcc_h1233 = _source173.dtor_value;
            {
              RAST._IExpr _out1308;
              DCOMP._IOwnership _out1309;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1310;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1308, out _out1309, out _out1310);
              r = _out1308;
              resultingOwnership = _out1309;
              readIdents = _out1310;
            }
          } else if (_source173.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3939___mcc_h1236 = _source173.dtor_args;
            DAST._IType _3940___mcc_h1237 = _source173.dtor_result;
            {
              RAST._IExpr _out1311;
              DCOMP._IOwnership _out1312;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1313;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1311, out _out1312, out _out1313);
              r = _out1311;
              resultingOwnership = _out1312;
              readIdents = _out1313;
            }
          } else if (_source173.is_Primitive) {
            DAST._IPrimitive _3941___mcc_h1240 = _source173.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out1314;
              DCOMP._IOwnership _out1315;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1316;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1314, out _out1315, out _out1316);
              r = _out1314;
              resultingOwnership = _out1315;
              readIdents = _out1316;
            }
          } else if (_source173.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3942___mcc_h1242 = _source173.dtor_Passthrough_i_a0;
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
            Dafny.ISequence<Dafny.Rune> _3943___mcc_h1244 = _source173.dtor_TypeArg_i_a0;
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
      Std.Wrappers._IOption<RAST._IType> _3944_tpe;
      _3944_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _3945_placeboOpt;
      _3945_placeboOpt = (((_3944_tpe).is_Some) ? (((_3944_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _3946_currentlyBorrowed;
      _3946_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _3947_noNeedOfClone;
      _3947_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_3945_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _3946_currentlyBorrowed = false;
        _3947_noNeedOfClone = true;
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        r = RAST.__default.BorrowMut(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        if (!(_3947_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_3947_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_3946_currentlyBorrowed) {
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
      DAST._IExpression _source175 = e;
      if (_source175.is_Literal) {
        DAST._ILiteral _3948___mcc_h0 = _source175.dtor_Literal_i_a0;
        RAST._IExpr _out1323;
        DCOMP._IOwnership _out1324;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1325;
        (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out1323, out _out1324, out _out1325);
        r = _out1323;
        resultingOwnership = _out1324;
        readIdents = _out1325;
      } else if (_source175.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _3949___mcc_h1 = _source175.dtor_Ident_i_a0;
        Dafny.ISequence<Dafny.Rune> _3950_name = _3949___mcc_h1;
        {
          RAST._IExpr _out1326;
          DCOMP._IOwnership _out1327;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1328;
          (this).GenIdent(DCOMP.__default.escapeName(_3950_name), selfIdent, env, expectedOwnership, out _out1326, out _out1327, out _out1328);
          r = _out1326;
          resultingOwnership = _out1327;
          readIdents = _out1328;
        }
      } else if (_source175.is_Companion) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3951___mcc_h2 = _source175.dtor_Companion_i_a0;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3952_path = _3951___mcc_h2;
        {
          RAST._IExpr _out1329;
          _out1329 = DCOMP.COMP.GenPathExpr(_3952_path);
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
      } else if (_source175.is_Tuple) {
        Dafny.ISequence<DAST._IExpression> _3953___mcc_h3 = _source175.dtor_Tuple_i_a0;
        Dafny.ISequence<DAST._IExpression> _3954_values = _3953___mcc_h3;
        {
          Dafny.ISequence<RAST._IExpr> _3955_exprs;
          _3955_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _hi30 = new BigInteger((_3954_values).Count);
          for (BigInteger _3956_i = BigInteger.Zero; _3956_i < _hi30; _3956_i++) {
            RAST._IExpr _3957_recursiveGen;
            DCOMP._IOwnership _3958___v111;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3959_recIdents;
            RAST._IExpr _out1332;
            DCOMP._IOwnership _out1333;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1334;
            (this).GenExpr((_3954_values).Select(_3956_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1332, out _out1333, out _out1334);
            _3957_recursiveGen = _out1332;
            _3958___v111 = _out1333;
            _3959_recIdents = _out1334;
            _3955_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_3955_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_3957_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3959_recIdents);
          }
          r = RAST.Expr.create_Tuple(_3955_exprs);
          RAST._IExpr _out1335;
          DCOMP._IOwnership _out1336;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1335, out _out1336);
          r = _out1335;
          resultingOwnership = _out1336;
          return ;
        }
      } else if (_source175.is_New) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3960___mcc_h4 = _source175.dtor_path;
        Dafny.ISequence<DAST._IType> _3961___mcc_h5 = _source175.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _3962___mcc_h6 = _source175.dtor_args;
        Dafny.ISequence<DAST._IExpression> _3963_args = _3962___mcc_h6;
        Dafny.ISequence<DAST._IType> _3964_typeArgs = _3961___mcc_h5;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3965_path = _3960___mcc_h4;
        {
          RAST._IExpr _out1337;
          _out1337 = DCOMP.COMP.GenPathExpr(_3965_path);
          r = _out1337;
          if ((new BigInteger((_3964_typeArgs).Count)).Sign == 1) {
            Dafny.ISequence<RAST._IType> _3966_typeExprs;
            _3966_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi31 = new BigInteger((_3964_typeArgs).Count);
            for (BigInteger _3967_i = BigInteger.Zero; _3967_i < _hi31; _3967_i++) {
              RAST._IType _3968_typeExpr;
              RAST._IType _out1338;
              _out1338 = (this).GenType((_3964_typeArgs).Select(_3967_i), false, false);
              _3968_typeExpr = _out1338;
              _3966_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_3966_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_3968_typeExpr));
            }
            r = (r).ApplyType(_3966_typeExprs);
          }
          r = (r).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_allocated"));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<RAST._IExpr> _3969_arguments;
          _3969_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi32 = new BigInteger((_3963_args).Count);
          for (BigInteger _3970_i = BigInteger.Zero; _3970_i < _hi32; _3970_i++) {
            RAST._IExpr _3971_recursiveGen;
            DCOMP._IOwnership _3972___v112;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3973_recIdents;
            RAST._IExpr _out1339;
            DCOMP._IOwnership _out1340;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1341;
            (this).GenExpr((_3963_args).Select(_3970_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1339, out _out1340, out _out1341);
            _3971_recursiveGen = _out1339;
            _3972___v112 = _out1340;
            _3973_recIdents = _out1341;
            _3969_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_3969_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_3971_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3973_recIdents);
          }
          r = (r).Apply(_3969_arguments);
          RAST._IExpr _out1342;
          DCOMP._IOwnership _out1343;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1342, out _out1343);
          r = _out1342;
          resultingOwnership = _out1343;
          return ;
        }
      } else if (_source175.is_NewArray) {
        Dafny.ISequence<DAST._IExpression> _3974___mcc_h7 = _source175.dtor_dims;
        DAST._IType _3975___mcc_h8 = _source175.dtor_typ;
        DAST._IType _3976_typ = _3975___mcc_h8;
        Dafny.ISequence<DAST._IExpression> _3977_dims = _3974___mcc_h7;
        {
          BigInteger _3978_i;
          _3978_i = (new BigInteger((_3977_dims).Count)) - (BigInteger.One);
          RAST._IType _3979_genTyp;
          RAST._IType _out1344;
          _out1344 = (this).GenType(_3976_typ, false, false);
          _3979_genTyp = _out1344;
          Dafny.ISequence<Dafny.Rune> _3980_s;
          _3980_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_3979_genTyp)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::std::default::Default>::default()"));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          while ((_3978_i).Sign != -1) {
            RAST._IExpr _3981_recursiveGen;
            DCOMP._IOwnership _3982___v113;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3983_recIdents;
            RAST._IExpr _out1345;
            DCOMP._IOwnership _out1346;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1347;
            (this).GenExpr((_3977_dims).Select(_3978_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1345, out _out1346, out _out1347);
            _3981_recursiveGen = _out1345;
            _3982___v113 = _out1346;
            _3983_recIdents = _out1347;
            _3980_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), _3980_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), (_3981_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3983_recIdents);
            _3978_i = (_3978_i) - (BigInteger.One);
          }
          r = RAST.Expr.create_RawExpr(_3980_s);
          RAST._IExpr _out1348;
          DCOMP._IOwnership _out1349;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1348, out _out1349);
          r = _out1348;
          resultingOwnership = _out1349;
        }
      } else if (_source175.is_DatatypeValue) {
        DAST._IDatatypeType _3984___mcc_h9 = _source175.dtor_datatypeType;
        Dafny.ISequence<DAST._IType> _3985___mcc_h10 = _source175.dtor_typeArgs;
        Dafny.ISequence<Dafny.Rune> _3986___mcc_h11 = _source175.dtor_variant;
        bool _3987___mcc_h12 = _source175.dtor_isCo;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _3988___mcc_h13 = _source175.dtor_contents;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _3989_values = _3988___mcc_h13;
        bool _3990_isCo = _3987___mcc_h12;
        Dafny.ISequence<Dafny.Rune> _3991_variant = _3986___mcc_h11;
        Dafny.ISequence<DAST._IType> _3992_typeArgs = _3985___mcc_h10;
        DAST._IDatatypeType _3993_datatypeType = _3984___mcc_h9;
        {
          RAST._IExpr _out1350;
          _out1350 = DCOMP.COMP.GenPathExpr((_3993_datatypeType).dtor_path);
          r = _out1350;
          Dafny.ISequence<RAST._IType> _3994_genTypeArgs;
          _3994_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _hi33 = new BigInteger((_3992_typeArgs).Count);
          for (BigInteger _3995_i = BigInteger.Zero; _3995_i < _hi33; _3995_i++) {
            RAST._IType _3996_typeExpr;
            RAST._IType _out1351;
            _out1351 = (this).GenType((_3992_typeArgs).Select(_3995_i), false, false);
            _3996_typeExpr = _out1351;
            _3994_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_3994_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_3996_typeExpr));
          }
          if ((new BigInteger((_3992_typeArgs).Count)).Sign == 1) {
            r = (r).ApplyType(_3994_genTypeArgs);
          }
          r = (r).MSel(DCOMP.__default.escapeName(_3991_variant));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<RAST._IAssignIdentifier> _3997_assignments;
          _3997_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
          BigInteger _hi34 = new BigInteger((_3989_values).Count);
          for (BigInteger _3998_i = BigInteger.Zero; _3998_i < _hi34; _3998_i++) {
            _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs63 = (_3989_values).Select(_3998_i);
            Dafny.ISequence<Dafny.Rune> _3999_name = _let_tmp_rhs63.dtor__0;
            DAST._IExpression _4000_value = _let_tmp_rhs63.dtor__1;
            if (_3990_isCo) {
              RAST._IExpr _4001_recursiveGen;
              DCOMP._IOwnership _4002___v114;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4003_recIdents;
              RAST._IExpr _out1352;
              DCOMP._IOwnership _out1353;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1354;
              (this).GenExpr(_4000_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out1352, out _out1353, out _out1354);
              _4001_recursiveGen = _out1352;
              _4002___v114 = _out1353;
              _4003_recIdents = _out1354;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4003_recIdents);
              Dafny.ISequence<Dafny.Rune> _4004_allReadCloned;
              _4004_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              while (!(_4003_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                Dafny.ISequence<Dafny.Rune> _4005_next;
                foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_4003_recIdents).Elements) {
                  _4005_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                  if ((_4003_recIdents).Contains(_4005_next)) {
                    goto after__ASSIGN_SUCH_THAT_2;
                  }
                }
                throw new System.Exception("assign-such-that search produced no value (line 3268)");
              after__ASSIGN_SUCH_THAT_2: ;
                _4004_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4004_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _4005_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _4005_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                _4003_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_4003_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_4005_next));
              }
              Dafny.ISequence<Dafny.Rune> _4006_assigned;
              _4006_assigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _4004_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_4001_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
              _3997_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_3997_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_3999_name, RAST.Expr.create_RawExpr(_4006_assigned))));
            } else {
              RAST._IExpr _4007_recursiveGen;
              DCOMP._IOwnership _4008___v115;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4009_recIdents;
              RAST._IExpr _out1355;
              DCOMP._IOwnership _out1356;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1357;
              (this).GenExpr(_4000_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1355, out _out1356, out _out1357);
              _4007_recursiveGen = _out1355;
              _4008___v115 = _out1356;
              _4009_recIdents = _out1357;
              _3997_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_3997_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_3999_name, _4007_recursiveGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4009_recIdents);
            }
          }
          r = RAST.Expr.create_StructBuild(r, _3997_assignments);
          r = RAST.__default.RcNew(r);
          RAST._IExpr _out1358;
          DCOMP._IOwnership _out1359;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1358, out _out1359);
          r = _out1358;
          resultingOwnership = _out1359;
          return ;
        }
      } else if (_source175.is_Convert) {
        DAST._IExpression _4010___mcc_h14 = _source175.dtor_value;
        DAST._IType _4011___mcc_h15 = _source175.dtor_from;
        DAST._IType _4012___mcc_h16 = _source175.dtor_typ;
        {
          RAST._IExpr _out1360;
          DCOMP._IOwnership _out1361;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1362;
          (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out1360, out _out1361, out _out1362);
          r = _out1360;
          resultingOwnership = _out1361;
          readIdents = _out1362;
        }
      } else if (_source175.is_SeqConstruct) {
        DAST._IExpression _4013___mcc_h17 = _source175.dtor_length;
        DAST._IExpression _4014___mcc_h18 = _source175.dtor_elem;
        DAST._IExpression _4015_expr = _4014___mcc_h18;
        DAST._IExpression _4016_length = _4013___mcc_h17;
        {
          RAST._IExpr _4017_recursiveGen;
          DCOMP._IOwnership _4018___v119;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4019_recIdents;
          RAST._IExpr _out1363;
          DCOMP._IOwnership _out1364;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1365;
          (this).GenExpr(_4015_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1363, out _out1364, out _out1365);
          _4017_recursiveGen = _out1363;
          _4018___v119 = _out1364;
          _4019_recIdents = _out1365;
          RAST._IExpr _4020_lengthGen;
          DCOMP._IOwnership _4021___v120;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4022_lengthIdents;
          RAST._IExpr _out1366;
          DCOMP._IOwnership _out1367;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1368;
          (this).GenExpr(_4016_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1366, out _out1367, out _out1368);
          _4020_lengthGen = _out1366;
          _4021___v120 = _out1367;
          _4022_lengthIdents = _out1368;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_4017_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_4020_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4019_recIdents, _4022_lengthIdents);
          RAST._IExpr _out1369;
          DCOMP._IOwnership _out1370;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1369, out _out1370);
          r = _out1369;
          resultingOwnership = _out1370;
          return ;
        }
      } else if (_source175.is_SeqValue) {
        Dafny.ISequence<DAST._IExpression> _4023___mcc_h19 = _source175.dtor_elements;
        DAST._IType _4024___mcc_h20 = _source175.dtor_typ;
        DAST._IType _4025_typ = _4024___mcc_h20;
        Dafny.ISequence<DAST._IExpression> _4026_exprs = _4023___mcc_h19;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          RAST._IType _4027_genTpe;
          RAST._IType _out1371;
          _out1371 = (this).GenType(_4025_typ, false, false);
          _4027_genTpe = _out1371;
          BigInteger _4028_i;
          _4028_i = BigInteger.Zero;
          Dafny.ISequence<RAST._IExpr> _4029_args;
          _4029_args = Dafny.Sequence<RAST._IExpr>.FromElements();
          while ((_4028_i) < (new BigInteger((_4026_exprs).Count))) {
            RAST._IExpr _4030_recursiveGen;
            DCOMP._IOwnership _4031___v121;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4032_recIdents;
            RAST._IExpr _out1372;
            DCOMP._IOwnership _out1373;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1374;
            (this).GenExpr((_4026_exprs).Select(_4028_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1372, out _out1373, out _out1374);
            _4030_recursiveGen = _out1372;
            _4031___v121 = _out1373;
            _4032_recIdents = _out1374;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4032_recIdents);
            _4029_args = Dafny.Sequence<RAST._IExpr>.Concat(_4029_args, Dafny.Sequence<RAST._IExpr>.FromElements(_4030_recursiveGen));
            _4028_i = (_4028_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_4029_args);
          if ((new BigInteger((_4029_args).Count)).Sign == 0) {
            r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_4027_genTpe));
          }
          RAST._IExpr _out1375;
          DCOMP._IOwnership _out1376;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1375, out _out1376);
          r = _out1375;
          resultingOwnership = _out1376;
          return ;
        }
      } else if (_source175.is_SetValue) {
        Dafny.ISequence<DAST._IExpression> _4033___mcc_h21 = _source175.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _4034_exprs = _4033___mcc_h21;
        {
          Dafny.ISequence<RAST._IExpr> _4035_generatedValues;
          _4035_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _4036_i;
          _4036_i = BigInteger.Zero;
          while ((_4036_i) < (new BigInteger((_4034_exprs).Count))) {
            RAST._IExpr _4037_recursiveGen;
            DCOMP._IOwnership _4038___v122;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4039_recIdents;
            RAST._IExpr _out1377;
            DCOMP._IOwnership _out1378;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1379;
            (this).GenExpr((_4034_exprs).Select(_4036_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1377, out _out1378, out _out1379);
            _4037_recursiveGen = _out1377;
            _4038___v122 = _out1378;
            _4039_recIdents = _out1379;
            _4035_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_4035_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_4037_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4039_recIdents);
            _4036_i = (_4036_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_4035_generatedValues);
          RAST._IExpr _out1380;
          DCOMP._IOwnership _out1381;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1380, out _out1381);
          r = _out1380;
          resultingOwnership = _out1381;
          return ;
        }
      } else if (_source175.is_MultisetValue) {
        Dafny.ISequence<DAST._IExpression> _4040___mcc_h22 = _source175.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _4041_exprs = _4040___mcc_h22;
        {
          Dafny.ISequence<RAST._IExpr> _4042_generatedValues;
          _4042_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _4043_i;
          _4043_i = BigInteger.Zero;
          while ((_4043_i) < (new BigInteger((_4041_exprs).Count))) {
            RAST._IExpr _4044_recursiveGen;
            DCOMP._IOwnership _4045___v123;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4046_recIdents;
            RAST._IExpr _out1382;
            DCOMP._IOwnership _out1383;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1384;
            (this).GenExpr((_4041_exprs).Select(_4043_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1382, out _out1383, out _out1384);
            _4044_recursiveGen = _out1382;
            _4045___v123 = _out1383;
            _4046_recIdents = _out1384;
            _4042_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_4042_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_4044_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4046_recIdents);
            _4043_i = (_4043_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_4042_generatedValues);
          RAST._IExpr _out1385;
          DCOMP._IOwnership _out1386;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1385, out _out1386);
          r = _out1385;
          resultingOwnership = _out1386;
          return ;
        }
      } else if (_source175.is_MapValue) {
        Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _4047___mcc_h23 = _source175.dtor_mapElems;
        Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _4048_mapElems = _4047___mcc_h23;
        {
          Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _4049_generatedValues;
          _4049_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _4050_i;
          _4050_i = BigInteger.Zero;
          while ((_4050_i) < (new BigInteger((_4048_mapElems).Count))) {
            RAST._IExpr _4051_recursiveGenKey;
            DCOMP._IOwnership _4052___v125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4053_recIdentsKey;
            RAST._IExpr _out1387;
            DCOMP._IOwnership _out1388;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1389;
            (this).GenExpr(((_4048_mapElems).Select(_4050_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1387, out _out1388, out _out1389);
            _4051_recursiveGenKey = _out1387;
            _4052___v125 = _out1388;
            _4053_recIdentsKey = _out1389;
            RAST._IExpr _4054_recursiveGenValue;
            DCOMP._IOwnership _4055___v126;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4056_recIdentsValue;
            RAST._IExpr _out1390;
            DCOMP._IOwnership _out1391;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1392;
            (this).GenExpr(((_4048_mapElems).Select(_4050_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1390, out _out1391, out _out1392);
            _4054_recursiveGenValue = _out1390;
            _4055___v126 = _out1391;
            _4056_recIdentsValue = _out1392;
            _4049_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_4049_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_4051_recursiveGenKey, _4054_recursiveGenValue)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4053_recIdentsKey), _4056_recIdentsValue);
            _4050_i = (_4050_i) + (BigInteger.One);
          }
          _4050_i = BigInteger.Zero;
          Dafny.ISequence<RAST._IExpr> _4057_arguments;
          _4057_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          while ((_4050_i) < (new BigInteger((_4049_generatedValues).Count))) {
            RAST._IExpr _4058_genKey;
            _4058_genKey = ((_4049_generatedValues).Select(_4050_i)).dtor__0;
            RAST._IExpr _4059_genValue;
            _4059_genValue = ((_4049_generatedValues).Select(_4050_i)).dtor__1;
            _4057_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_4057_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _4058_genKey, _4059_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
            _4050_i = (_4050_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_4057_arguments);
          RAST._IExpr _out1393;
          DCOMP._IOwnership _out1394;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1393, out _out1394);
          r = _out1393;
          resultingOwnership = _out1394;
          return ;
        }
      } else if (_source175.is_MapBuilder) {
        DAST._IType _4060___mcc_h24 = _source175.dtor_keyType;
        DAST._IType _4061___mcc_h25 = _source175.dtor_valueType;
        DAST._IType _4062_valueType = _4061___mcc_h25;
        DAST._IType _4063_keyType = _4060___mcc_h24;
        {
          RAST._IType _4064_kType;
          RAST._IType _out1395;
          _out1395 = (this).GenType(_4063_keyType, false, false);
          _4064_kType = _out1395;
          RAST._IType _4065_vType;
          RAST._IType _out1396;
          _out1396 = (this).GenType(_4062_valueType, false, false);
          _4065_vType = _out1396;
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_4064_kType, _4065_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1397;
          DCOMP._IOwnership _out1398;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1397, out _out1398);
          r = _out1397;
          resultingOwnership = _out1398;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source175.is_SeqUpdate) {
        DAST._IExpression _4066___mcc_h26 = _source175.dtor_expr;
        DAST._IExpression _4067___mcc_h27 = _source175.dtor_indexExpr;
        DAST._IExpression _4068___mcc_h28 = _source175.dtor_value;
        DAST._IExpression _4069_value = _4068___mcc_h28;
        DAST._IExpression _4070_index = _4067___mcc_h27;
        DAST._IExpression _4071_expr = _4066___mcc_h26;
        {
          RAST._IExpr _4072_exprR;
          DCOMP._IOwnership _4073___v127;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4074_exprIdents;
          RAST._IExpr _out1399;
          DCOMP._IOwnership _out1400;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1401;
          (this).GenExpr(_4071_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1399, out _out1400, out _out1401);
          _4072_exprR = _out1399;
          _4073___v127 = _out1400;
          _4074_exprIdents = _out1401;
          RAST._IExpr _4075_indexR;
          DCOMP._IOwnership _4076_indexOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4077_indexIdents;
          RAST._IExpr _out1402;
          DCOMP._IOwnership _out1403;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1404;
          (this).GenExpr(_4070_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1402, out _out1403, out _out1404);
          _4075_indexR = _out1402;
          _4076_indexOwnership = _out1403;
          _4077_indexIdents = _out1404;
          RAST._IExpr _4078_valueR;
          DCOMP._IOwnership _4079_valueOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4080_valueIdents;
          RAST._IExpr _out1405;
          DCOMP._IOwnership _out1406;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1407;
          (this).GenExpr(_4069_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1405, out _out1406, out _out1407);
          _4078_valueR = _out1405;
          _4079_valueOwnership = _out1406;
          _4080_valueIdents = _out1407;
          r = ((_4072_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_4075_indexR, _4078_valueR));
          RAST._IExpr _out1408;
          DCOMP._IOwnership _out1409;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1408, out _out1409);
          r = _out1408;
          resultingOwnership = _out1409;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4074_exprIdents, _4077_indexIdents), _4080_valueIdents);
          return ;
        }
      } else if (_source175.is_MapUpdate) {
        DAST._IExpression _4081___mcc_h29 = _source175.dtor_expr;
        DAST._IExpression _4082___mcc_h30 = _source175.dtor_indexExpr;
        DAST._IExpression _4083___mcc_h31 = _source175.dtor_value;
        DAST._IExpression _4084_value = _4083___mcc_h31;
        DAST._IExpression _4085_index = _4082___mcc_h30;
        DAST._IExpression _4086_expr = _4081___mcc_h29;
        {
          RAST._IExpr _4087_exprR;
          DCOMP._IOwnership _4088___v128;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4089_exprIdents;
          RAST._IExpr _out1410;
          DCOMP._IOwnership _out1411;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1412;
          (this).GenExpr(_4086_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1410, out _out1411, out _out1412);
          _4087_exprR = _out1410;
          _4088___v128 = _out1411;
          _4089_exprIdents = _out1412;
          RAST._IExpr _4090_indexR;
          DCOMP._IOwnership _4091_indexOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4092_indexIdents;
          RAST._IExpr _out1413;
          DCOMP._IOwnership _out1414;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1415;
          (this).GenExpr(_4085_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1413, out _out1414, out _out1415);
          _4090_indexR = _out1413;
          _4091_indexOwnership = _out1414;
          _4092_indexIdents = _out1415;
          RAST._IExpr _4093_valueR;
          DCOMP._IOwnership _4094_valueOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4095_valueIdents;
          RAST._IExpr _out1416;
          DCOMP._IOwnership _out1417;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1418;
          (this).GenExpr(_4084_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1416, out _out1417, out _out1418);
          _4093_valueR = _out1416;
          _4094_valueOwnership = _out1417;
          _4095_valueIdents = _out1418;
          r = ((_4087_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_4090_indexR, _4093_valueR));
          RAST._IExpr _out1419;
          DCOMP._IOwnership _out1420;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1419, out _out1420);
          r = _out1419;
          resultingOwnership = _out1420;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4089_exprIdents, _4092_indexIdents), _4095_valueIdents);
          return ;
        }
      } else if (_source175.is_SetBuilder) {
        DAST._IType _4096___mcc_h32 = _source175.dtor_elemType;
        DAST._IType _4097_elemType = _4096___mcc_h32;
        {
          RAST._IType _4098_eType;
          RAST._IType _out1421;
          _out1421 = (this).GenType(_4097_elemType, false, false);
          _4098_eType = _out1421;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_4098_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1422;
          DCOMP._IOwnership _out1423;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1422, out _out1423);
          r = _out1422;
          resultingOwnership = _out1423;
          return ;
        }
      } else if (_source175.is_ToMultiset) {
        DAST._IExpression _4099___mcc_h33 = _source175.dtor_ToMultiset_i_a0;
        DAST._IExpression _4100_expr = _4099___mcc_h33;
        {
          RAST._IExpr _4101_recursiveGen;
          DCOMP._IOwnership _4102___v124;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4103_recIdents;
          RAST._IExpr _out1424;
          DCOMP._IOwnership _out1425;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1426;
          (this).GenExpr(_4100_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1424, out _out1425, out _out1426);
          _4101_recursiveGen = _out1424;
          _4102___v124 = _out1425;
          _4103_recIdents = _out1426;
          r = ((_4101_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          readIdents = _4103_recIdents;
          RAST._IExpr _out1427;
          DCOMP._IOwnership _out1428;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1427, out _out1428);
          r = _out1427;
          resultingOwnership = _out1428;
          return ;
        }
      } else if (_source175.is_This) {
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source176 = selfIdent;
          if (_source176.is_None) {
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
            Dafny.ISequence<Dafny.Rune> _4104___mcc_h279 = _source176.dtor_value;
            Dafny.ISequence<Dafny.Rune> _4105_id = _4104___mcc_h279;
            {
              r = RAST.Expr.create_Identifier(_4105_id);
              if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
                r = RAST.__default.Clone(r);
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
                r = RAST.__default.BoxNew(RAST.__default.Clone(r));
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
              } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
                if (!(_4105_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  r = RAST.__default.Borrow(r);
                }
                resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              } else {
                if (!(_4105_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  r = RAST.__default.BorrowMut(r);
                }
                resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
              }
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_4105_id);
            }
          }
          return ;
        }
      } else if (_source175.is_Ite) {
        DAST._IExpression _4106___mcc_h34 = _source175.dtor_cond;
        DAST._IExpression _4107___mcc_h35 = _source175.dtor_thn;
        DAST._IExpression _4108___mcc_h36 = _source175.dtor_els;
        DAST._IExpression _4109_f = _4108___mcc_h36;
        DAST._IExpression _4110_t = _4107___mcc_h35;
        DAST._IExpression _4111_cond = _4106___mcc_h34;
        {
          RAST._IExpr _4112_cond;
          DCOMP._IOwnership _4113___v129;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4114_recIdentsCond;
          RAST._IExpr _out1431;
          DCOMP._IOwnership _out1432;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1433;
          (this).GenExpr(_4111_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1431, out _out1432, out _out1433);
          _4112_cond = _out1431;
          _4113___v129 = _out1432;
          _4114_recIdentsCond = _out1433;
          Dafny.ISequence<Dafny.Rune> _4115_condString;
          _4115_condString = (_4112_cond)._ToString(DCOMP.__default.IND);
          RAST._IExpr _4116___v130;
          DCOMP._IOwnership _4117_tHasToBeOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4118___v131;
          RAST._IExpr _out1434;
          DCOMP._IOwnership _out1435;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1436;
          (this).GenExpr(_4110_t, selfIdent, env, expectedOwnership, out _out1434, out _out1435, out _out1436);
          _4116___v130 = _out1434;
          _4117_tHasToBeOwned = _out1435;
          _4118___v131 = _out1436;
          RAST._IExpr _4119_fExpr;
          DCOMP._IOwnership _4120_fOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4121_recIdentsF;
          RAST._IExpr _out1437;
          DCOMP._IOwnership _out1438;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1439;
          (this).GenExpr(_4109_f, selfIdent, env, _4117_tHasToBeOwned, out _out1437, out _out1438, out _out1439);
          _4119_fExpr = _out1437;
          _4120_fOwned = _out1438;
          _4121_recIdentsF = _out1439;
          Dafny.ISequence<Dafny.Rune> _4122_fString;
          _4122_fString = (_4119_fExpr)._ToString(DCOMP.__default.IND);
          RAST._IExpr _4123_tExpr;
          DCOMP._IOwnership _4124___v132;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4125_recIdentsT;
          RAST._IExpr _out1440;
          DCOMP._IOwnership _out1441;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1442;
          (this).GenExpr(_4110_t, selfIdent, env, _4120_fOwned, out _out1440, out _out1441, out _out1442);
          _4123_tExpr = _out1440;
          _4124___v132 = _out1441;
          _4125_recIdentsT = _out1442;
          Dafny.ISequence<Dafny.Rune> _4126_tString;
          _4126_tString = (_4123_tExpr)._ToString(DCOMP.__default.IND);
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _4115_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _4126_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _4122_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})")));
          RAST._IExpr _out1443;
          DCOMP._IOwnership _out1444;
          DCOMP.COMP.FromOwnership(r, _4120_fOwned, expectedOwnership, out _out1443, out _out1444);
          r = _out1443;
          resultingOwnership = _out1444;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4114_recIdentsCond, _4125_recIdentsT), _4121_recIdentsF);
          return ;
        }
      } else if (_source175.is_UnOp) {
        DAST._IUnaryOp _4127___mcc_h37 = _source175.dtor_unOp;
        DAST._IExpression _4128___mcc_h38 = _source175.dtor_expr;
        DAST.Format._IUnaryOpFormat _4129___mcc_h39 = _source175.dtor_format1;
        DAST._IUnaryOp _source177 = _4127___mcc_h37;
        if (_source177.is_Not) {
          DAST.Format._IUnaryOpFormat _4130_format = _4129___mcc_h39;
          DAST._IExpression _4131_e = _4128___mcc_h38;
          {
            RAST._IExpr _4132_recursiveGen;
            DCOMP._IOwnership _4133___v133;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4134_recIdents;
            RAST._IExpr _out1445;
            DCOMP._IOwnership _out1446;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1447;
            (this).GenExpr(_4131_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1445, out _out1446, out _out1447);
            _4132_recursiveGen = _out1445;
            _4133___v133 = _out1446;
            _4134_recIdents = _out1447;
            r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _4132_recursiveGen, _4130_format);
            RAST._IExpr _out1448;
            DCOMP._IOwnership _out1449;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1448, out _out1449);
            r = _out1448;
            resultingOwnership = _out1449;
            readIdents = _4134_recIdents;
            return ;
          }
        } else if (_source177.is_BitwiseNot) {
          DAST.Format._IUnaryOpFormat _4135_format = _4129___mcc_h39;
          DAST._IExpression _4136_e = _4128___mcc_h38;
          {
            RAST._IExpr _4137_recursiveGen;
            DCOMP._IOwnership _4138___v134;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4139_recIdents;
            RAST._IExpr _out1450;
            DCOMP._IOwnership _out1451;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1452;
            (this).GenExpr(_4136_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1450, out _out1451, out _out1452);
            _4137_recursiveGen = _out1450;
            _4138___v134 = _out1451;
            _4139_recIdents = _out1452;
            r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _4137_recursiveGen, _4135_format);
            RAST._IExpr _out1453;
            DCOMP._IOwnership _out1454;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1453, out _out1454);
            r = _out1453;
            resultingOwnership = _out1454;
            readIdents = _4139_recIdents;
            return ;
          }
        } else {
          DAST.Format._IUnaryOpFormat _4140_format = _4129___mcc_h39;
          DAST._IExpression _4141_e = _4128___mcc_h38;
          {
            RAST._IExpr _4142_recursiveGen;
            DCOMP._IOwnership _4143_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4144_recIdents;
            RAST._IExpr _out1455;
            DCOMP._IOwnership _out1456;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1457;
            (this).GenExpr(_4141_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1455, out _out1456, out _out1457);
            _4142_recursiveGen = _out1455;
            _4143_recOwned = _out1456;
            _4144_recIdents = _out1457;
            r = ((_4142_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out1458;
            DCOMP._IOwnership _out1459;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1458, out _out1459);
            r = _out1458;
            resultingOwnership = _out1459;
            readIdents = _4144_recIdents;
            return ;
          }
        }
      } else if (_source175.is_BinOp) {
        DAST._IBinOp _4145___mcc_h40 = _source175.dtor_op;
        DAST._IExpression _4146___mcc_h41 = _source175.dtor_left;
        DAST._IExpression _4147___mcc_h42 = _source175.dtor_right;
        DAST.Format._IBinaryOpFormat _4148___mcc_h43 = _source175.dtor_format2;
        RAST._IExpr _out1460;
        DCOMP._IOwnership _out1461;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1462;
        (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out1460, out _out1461, out _out1462);
        r = _out1460;
        resultingOwnership = _out1461;
        readIdents = _out1462;
      } else if (_source175.is_ArrayLen) {
        DAST._IExpression _4149___mcc_h44 = _source175.dtor_expr;
        BigInteger _4150___mcc_h45 = _source175.dtor_dim;
        BigInteger _4151_dim = _4150___mcc_h45;
        DAST._IExpression _4152_expr = _4149___mcc_h44;
        {
          RAST._IExpr _4153_recursiveGen;
          DCOMP._IOwnership _4154___v139;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4155_recIdents;
          RAST._IExpr _out1463;
          DCOMP._IOwnership _out1464;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1465;
          (this).GenExpr(_4152_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1463, out _out1464, out _out1465);
          _4153_recursiveGen = _out1463;
          _4154___v139 = _out1464;
          _4155_recIdents = _out1465;
          if ((_4151_dim).Sign == 0) {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), (_4153_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())")));
          } else {
            Dafny.ISequence<Dafny.Rune> _4156_s;
            _4156_s = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(m.borrow().len())")))._ToString(DCOMP.__default.IND);
            BigInteger _4157_i;
            _4157_i = BigInteger.One;
            while ((_4157_i) < (_4151_dim)) {
              _4156_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("m.borrow().get(0).map(|m| "), _4156_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"));
              _4157_i = (_4157_i) + (BigInteger.One);
            }
            r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_4153_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow().get(0).map(|m| ")), _4156_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"))));
          }
          RAST._IExpr _out1466;
          DCOMP._IOwnership _out1467;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1466, out _out1467);
          r = _out1466;
          resultingOwnership = _out1467;
          readIdents = _4155_recIdents;
          return ;
        }
      } else if (_source175.is_MapKeys) {
        DAST._IExpression _4158___mcc_h46 = _source175.dtor_expr;
        DAST._IExpression _4159_expr = _4158___mcc_h46;
        {
          RAST._IExpr _4160_recursiveGen;
          DCOMP._IOwnership _4161___v140;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4162_recIdents;
          RAST._IExpr _out1468;
          DCOMP._IOwnership _out1469;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1470;
          (this).GenExpr(_4159_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1468, out _out1469, out _out1470);
          _4160_recursiveGen = _out1468;
          _4161___v140 = _out1469;
          _4162_recIdents = _out1470;
          readIdents = _4162_recIdents;
          r = ((_4160_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1471;
          DCOMP._IOwnership _out1472;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1471, out _out1472);
          r = _out1471;
          resultingOwnership = _out1472;
          return ;
        }
      } else if (_source175.is_MapValues) {
        DAST._IExpression _4163___mcc_h47 = _source175.dtor_expr;
        DAST._IExpression _4164_expr = _4163___mcc_h47;
        {
          RAST._IExpr _4165_recursiveGen;
          DCOMP._IOwnership _4166___v141;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4167_recIdents;
          RAST._IExpr _out1473;
          DCOMP._IOwnership _out1474;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1475;
          (this).GenExpr(_4164_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1473, out _out1474, out _out1475);
          _4165_recursiveGen = _out1473;
          _4166___v141 = _out1474;
          _4167_recIdents = _out1475;
          readIdents = _4167_recIdents;
          r = ((_4165_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1476;
          DCOMP._IOwnership _out1477;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1476, out _out1477);
          r = _out1476;
          resultingOwnership = _out1477;
          return ;
        }
      } else if (_source175.is_Select) {
        DAST._IExpression _4168___mcc_h48 = _source175.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _4169___mcc_h49 = _source175.dtor_field;
        bool _4170___mcc_h50 = _source175.dtor_isConstant;
        bool _4171___mcc_h51 = _source175.dtor_onDatatype;
        DAST._IType _4172___mcc_h52 = _source175.dtor_fieldType;
        DAST._IExpression _source178 = _4168___mcc_h48;
        if (_source178.is_Literal) {
          DAST._ILiteral _4173___mcc_h53 = _source178.dtor_Literal_i_a0;
          DAST._IType _4174_fieldType = _4172___mcc_h52;
          bool _4175_isDatatype = _4171___mcc_h51;
          bool _4176_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4177_field = _4169___mcc_h49;
          DAST._IExpression _4178_on = _4168___mcc_h48;
          {
            if (_4175_isDatatype) {
              RAST._IExpr _4179_onExpr;
              DCOMP._IOwnership _4180_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4181_recIdents;
              RAST._IExpr _out1478;
              DCOMP._IOwnership _out1479;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1480;
              (this).GenExpr(_4178_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1478, out _out1479, out _out1480);
              _4179_onExpr = _out1478;
              _4180_onOwned = _out1479;
              _4181_recIdents = _out1480;
              r = ((_4179_onExpr).Sel(DCOMP.__default.escapeName(_4177_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4182_typ;
              RAST._IType _out1481;
              _out1481 = (this).GenType(_4174_fieldType, false, false);
              _4182_typ = _out1481;
              if (((_4182_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1482;
                DCOMP._IOwnership _out1483;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1482, out _out1483);
                r = _out1482;
                resultingOwnership = _out1483;
              }
              readIdents = _4181_recIdents;
            } else {
              RAST._IExpr _4183_onExpr;
              DCOMP._IOwnership _4184_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4185_recIdents;
              RAST._IExpr _out1484;
              DCOMP._IOwnership _out1485;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1486;
              (this).GenExpr(_4178_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1484, out _out1485, out _out1486);
              _4183_onExpr = _out1484;
              _4184_onOwned = _out1485;
              _4185_recIdents = _out1486;
              r = _4183_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4177_field));
              if (_4176_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4186_s;
                _4186_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4183_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4177_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4186_s);
              }
              DCOMP._IOwnership _4187_fromOwnership;
              _4187_fromOwnership = ((_4176_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1487;
              DCOMP._IOwnership _out1488;
              DCOMP.COMP.FromOwnership(r, _4187_fromOwnership, expectedOwnership, out _out1487, out _out1488);
              r = _out1487;
              resultingOwnership = _out1488;
              readIdents = _4185_recIdents;
            }
            return ;
          }
        } else if (_source178.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _4188___mcc_h55 = _source178.dtor_Ident_i_a0;
          DAST._IType _4189_fieldType = _4172___mcc_h52;
          bool _4190_isDatatype = _4171___mcc_h51;
          bool _4191_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4192_field = _4169___mcc_h49;
          DAST._IExpression _4193_on = _4168___mcc_h48;
          {
            if (_4190_isDatatype) {
              RAST._IExpr _4194_onExpr;
              DCOMP._IOwnership _4195_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4196_recIdents;
              RAST._IExpr _out1489;
              DCOMP._IOwnership _out1490;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1491;
              (this).GenExpr(_4193_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1489, out _out1490, out _out1491);
              _4194_onExpr = _out1489;
              _4195_onOwned = _out1490;
              _4196_recIdents = _out1491;
              r = ((_4194_onExpr).Sel(DCOMP.__default.escapeName(_4192_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4197_typ;
              RAST._IType _out1492;
              _out1492 = (this).GenType(_4189_fieldType, false, false);
              _4197_typ = _out1492;
              if (((_4197_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1493;
                DCOMP._IOwnership _out1494;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1493, out _out1494);
                r = _out1493;
                resultingOwnership = _out1494;
              }
              readIdents = _4196_recIdents;
            } else {
              RAST._IExpr _4198_onExpr;
              DCOMP._IOwnership _4199_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4200_recIdents;
              RAST._IExpr _out1495;
              DCOMP._IOwnership _out1496;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1497;
              (this).GenExpr(_4193_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1495, out _out1496, out _out1497);
              _4198_onExpr = _out1495;
              _4199_onOwned = _out1496;
              _4200_recIdents = _out1497;
              r = _4198_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4192_field));
              if (_4191_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4201_s;
                _4201_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4198_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4192_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4201_s);
              }
              DCOMP._IOwnership _4202_fromOwnership;
              _4202_fromOwnership = ((_4191_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1498;
              DCOMP._IOwnership _out1499;
              DCOMP.COMP.FromOwnership(r, _4202_fromOwnership, expectedOwnership, out _out1498, out _out1499);
              r = _out1498;
              resultingOwnership = _out1499;
              readIdents = _4200_recIdents;
            }
            return ;
          }
        } else if (_source178.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4203___mcc_h57 = _source178.dtor_Companion_i_a0;
          DAST._IType _4204_fieldType = _4172___mcc_h52;
          bool _4205_isDatatype = _4171___mcc_h51;
          bool _4206_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4207_field = _4169___mcc_h49;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4208_c = _4203___mcc_h57;
          {
            RAST._IExpr _4209_onExpr;
            DCOMP._IOwnership _4210_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4211_recIdents;
            RAST._IExpr _out1500;
            DCOMP._IOwnership _out1501;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1502;
            (this).GenExpr(DAST.Expression.create_Companion(_4208_c), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1500, out _out1501, out _out1502);
            _4209_onExpr = _out1500;
            _4210_onOwned = _out1501;
            _4211_recIdents = _out1502;
            r = ((_4209_onExpr).MSel(DCOMP.__default.escapeName(_4207_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out1503;
            DCOMP._IOwnership _out1504;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1503, out _out1504);
            r = _out1503;
            resultingOwnership = _out1504;
            readIdents = _4211_recIdents;
            return ;
          }
        } else if (_source178.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _4212___mcc_h59 = _source178.dtor_Tuple_i_a0;
          DAST._IType _4213_fieldType = _4172___mcc_h52;
          bool _4214_isDatatype = _4171___mcc_h51;
          bool _4215_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4216_field = _4169___mcc_h49;
          DAST._IExpression _4217_on = _4168___mcc_h48;
          {
            if (_4214_isDatatype) {
              RAST._IExpr _4218_onExpr;
              DCOMP._IOwnership _4219_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4220_recIdents;
              RAST._IExpr _out1505;
              DCOMP._IOwnership _out1506;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1507;
              (this).GenExpr(_4217_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1505, out _out1506, out _out1507);
              _4218_onExpr = _out1505;
              _4219_onOwned = _out1506;
              _4220_recIdents = _out1507;
              r = ((_4218_onExpr).Sel(DCOMP.__default.escapeName(_4216_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4221_typ;
              RAST._IType _out1508;
              _out1508 = (this).GenType(_4213_fieldType, false, false);
              _4221_typ = _out1508;
              if (((_4221_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1509;
                DCOMP._IOwnership _out1510;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1509, out _out1510);
                r = _out1509;
                resultingOwnership = _out1510;
              }
              readIdents = _4220_recIdents;
            } else {
              RAST._IExpr _4222_onExpr;
              DCOMP._IOwnership _4223_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4224_recIdents;
              RAST._IExpr _out1511;
              DCOMP._IOwnership _out1512;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1513;
              (this).GenExpr(_4217_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1511, out _out1512, out _out1513);
              _4222_onExpr = _out1511;
              _4223_onOwned = _out1512;
              _4224_recIdents = _out1513;
              r = _4222_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4216_field));
              if (_4215_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4225_s;
                _4225_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4222_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4216_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4225_s);
              }
              DCOMP._IOwnership _4226_fromOwnership;
              _4226_fromOwnership = ((_4215_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1514;
              DCOMP._IOwnership _out1515;
              DCOMP.COMP.FromOwnership(r, _4226_fromOwnership, expectedOwnership, out _out1514, out _out1515);
              r = _out1514;
              resultingOwnership = _out1515;
              readIdents = _4224_recIdents;
            }
            return ;
          }
        } else if (_source178.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4227___mcc_h61 = _source178.dtor_path;
          Dafny.ISequence<DAST._IType> _4228___mcc_h62 = _source178.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _4229___mcc_h63 = _source178.dtor_args;
          DAST._IType _4230_fieldType = _4172___mcc_h52;
          bool _4231_isDatatype = _4171___mcc_h51;
          bool _4232_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4233_field = _4169___mcc_h49;
          DAST._IExpression _4234_on = _4168___mcc_h48;
          {
            if (_4231_isDatatype) {
              RAST._IExpr _4235_onExpr;
              DCOMP._IOwnership _4236_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4237_recIdents;
              RAST._IExpr _out1516;
              DCOMP._IOwnership _out1517;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1518;
              (this).GenExpr(_4234_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1516, out _out1517, out _out1518);
              _4235_onExpr = _out1516;
              _4236_onOwned = _out1517;
              _4237_recIdents = _out1518;
              r = ((_4235_onExpr).Sel(DCOMP.__default.escapeName(_4233_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4238_typ;
              RAST._IType _out1519;
              _out1519 = (this).GenType(_4230_fieldType, false, false);
              _4238_typ = _out1519;
              if (((_4238_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1520;
                DCOMP._IOwnership _out1521;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1520, out _out1521);
                r = _out1520;
                resultingOwnership = _out1521;
              }
              readIdents = _4237_recIdents;
            } else {
              RAST._IExpr _4239_onExpr;
              DCOMP._IOwnership _4240_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4241_recIdents;
              RAST._IExpr _out1522;
              DCOMP._IOwnership _out1523;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1524;
              (this).GenExpr(_4234_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1522, out _out1523, out _out1524);
              _4239_onExpr = _out1522;
              _4240_onOwned = _out1523;
              _4241_recIdents = _out1524;
              r = _4239_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4233_field));
              if (_4232_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4242_s;
                _4242_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4239_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4233_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4242_s);
              }
              DCOMP._IOwnership _4243_fromOwnership;
              _4243_fromOwnership = ((_4232_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1525;
              DCOMP._IOwnership _out1526;
              DCOMP.COMP.FromOwnership(r, _4243_fromOwnership, expectedOwnership, out _out1525, out _out1526);
              r = _out1525;
              resultingOwnership = _out1526;
              readIdents = _4241_recIdents;
            }
            return ;
          }
        } else if (_source178.is_NewArray) {
          Dafny.ISequence<DAST._IExpression> _4244___mcc_h67 = _source178.dtor_dims;
          DAST._IType _4245___mcc_h68 = _source178.dtor_typ;
          DAST._IType _4246_fieldType = _4172___mcc_h52;
          bool _4247_isDatatype = _4171___mcc_h51;
          bool _4248_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4249_field = _4169___mcc_h49;
          DAST._IExpression _4250_on = _4168___mcc_h48;
          {
            if (_4247_isDatatype) {
              RAST._IExpr _4251_onExpr;
              DCOMP._IOwnership _4252_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4253_recIdents;
              RAST._IExpr _out1527;
              DCOMP._IOwnership _out1528;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1529;
              (this).GenExpr(_4250_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1527, out _out1528, out _out1529);
              _4251_onExpr = _out1527;
              _4252_onOwned = _out1528;
              _4253_recIdents = _out1529;
              r = ((_4251_onExpr).Sel(DCOMP.__default.escapeName(_4249_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4254_typ;
              RAST._IType _out1530;
              _out1530 = (this).GenType(_4246_fieldType, false, false);
              _4254_typ = _out1530;
              if (((_4254_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1531;
                DCOMP._IOwnership _out1532;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1531, out _out1532);
                r = _out1531;
                resultingOwnership = _out1532;
              }
              readIdents = _4253_recIdents;
            } else {
              RAST._IExpr _4255_onExpr;
              DCOMP._IOwnership _4256_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4257_recIdents;
              RAST._IExpr _out1533;
              DCOMP._IOwnership _out1534;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1535;
              (this).GenExpr(_4250_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1533, out _out1534, out _out1535);
              _4255_onExpr = _out1533;
              _4256_onOwned = _out1534;
              _4257_recIdents = _out1535;
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
              RAST._IExpr _out1536;
              DCOMP._IOwnership _out1537;
              DCOMP.COMP.FromOwnership(r, _4259_fromOwnership, expectedOwnership, out _out1536, out _out1537);
              r = _out1536;
              resultingOwnership = _out1537;
              readIdents = _4257_recIdents;
            }
            return ;
          }
        } else if (_source178.is_DatatypeValue) {
          DAST._IDatatypeType _4260___mcc_h71 = _source178.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _4261___mcc_h72 = _source178.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _4262___mcc_h73 = _source178.dtor_variant;
          bool _4263___mcc_h74 = _source178.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _4264___mcc_h75 = _source178.dtor_contents;
          DAST._IType _4265_fieldType = _4172___mcc_h52;
          bool _4266_isDatatype = _4171___mcc_h51;
          bool _4267_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4268_field = _4169___mcc_h49;
          DAST._IExpression _4269_on = _4168___mcc_h48;
          {
            if (_4266_isDatatype) {
              RAST._IExpr _4270_onExpr;
              DCOMP._IOwnership _4271_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4272_recIdents;
              RAST._IExpr _out1538;
              DCOMP._IOwnership _out1539;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1540;
              (this).GenExpr(_4269_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1538, out _out1539, out _out1540);
              _4270_onExpr = _out1538;
              _4271_onOwned = _out1539;
              _4272_recIdents = _out1540;
              r = ((_4270_onExpr).Sel(DCOMP.__default.escapeName(_4268_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4273_typ;
              RAST._IType _out1541;
              _out1541 = (this).GenType(_4265_fieldType, false, false);
              _4273_typ = _out1541;
              if (((_4273_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1542;
                DCOMP._IOwnership _out1543;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1542, out _out1543);
                r = _out1542;
                resultingOwnership = _out1543;
              }
              readIdents = _4272_recIdents;
            } else {
              RAST._IExpr _4274_onExpr;
              DCOMP._IOwnership _4275_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4276_recIdents;
              RAST._IExpr _out1544;
              DCOMP._IOwnership _out1545;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1546;
              (this).GenExpr(_4269_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1544, out _out1545, out _out1546);
              _4274_onExpr = _out1544;
              _4275_onOwned = _out1545;
              _4276_recIdents = _out1546;
              r = _4274_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4268_field));
              if (_4267_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4277_s;
                _4277_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4274_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4268_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4277_s);
              }
              DCOMP._IOwnership _4278_fromOwnership;
              _4278_fromOwnership = ((_4267_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1547;
              DCOMP._IOwnership _out1548;
              DCOMP.COMP.FromOwnership(r, _4278_fromOwnership, expectedOwnership, out _out1547, out _out1548);
              r = _out1547;
              resultingOwnership = _out1548;
              readIdents = _4276_recIdents;
            }
            return ;
          }
        } else if (_source178.is_Convert) {
          DAST._IExpression _4279___mcc_h81 = _source178.dtor_value;
          DAST._IType _4280___mcc_h82 = _source178.dtor_from;
          DAST._IType _4281___mcc_h83 = _source178.dtor_typ;
          DAST._IType _4282_fieldType = _4172___mcc_h52;
          bool _4283_isDatatype = _4171___mcc_h51;
          bool _4284_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4285_field = _4169___mcc_h49;
          DAST._IExpression _4286_on = _4168___mcc_h48;
          {
            if (_4283_isDatatype) {
              RAST._IExpr _4287_onExpr;
              DCOMP._IOwnership _4288_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4289_recIdents;
              RAST._IExpr _out1549;
              DCOMP._IOwnership _out1550;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1551;
              (this).GenExpr(_4286_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1549, out _out1550, out _out1551);
              _4287_onExpr = _out1549;
              _4288_onOwned = _out1550;
              _4289_recIdents = _out1551;
              r = ((_4287_onExpr).Sel(DCOMP.__default.escapeName(_4285_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4290_typ;
              RAST._IType _out1552;
              _out1552 = (this).GenType(_4282_fieldType, false, false);
              _4290_typ = _out1552;
              if (((_4290_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1553;
                DCOMP._IOwnership _out1554;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1553, out _out1554);
                r = _out1553;
                resultingOwnership = _out1554;
              }
              readIdents = _4289_recIdents;
            } else {
              RAST._IExpr _4291_onExpr;
              DCOMP._IOwnership _4292_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4293_recIdents;
              RAST._IExpr _out1555;
              DCOMP._IOwnership _out1556;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1557;
              (this).GenExpr(_4286_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1555, out _out1556, out _out1557);
              _4291_onExpr = _out1555;
              _4292_onOwned = _out1556;
              _4293_recIdents = _out1557;
              r = _4291_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4285_field));
              if (_4284_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4294_s;
                _4294_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4291_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4285_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4294_s);
              }
              DCOMP._IOwnership _4295_fromOwnership;
              _4295_fromOwnership = ((_4284_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1558;
              DCOMP._IOwnership _out1559;
              DCOMP.COMP.FromOwnership(r, _4295_fromOwnership, expectedOwnership, out _out1558, out _out1559);
              r = _out1558;
              resultingOwnership = _out1559;
              readIdents = _4293_recIdents;
            }
            return ;
          }
        } else if (_source178.is_SeqConstruct) {
          DAST._IExpression _4296___mcc_h87 = _source178.dtor_length;
          DAST._IExpression _4297___mcc_h88 = _source178.dtor_elem;
          DAST._IType _4298_fieldType = _4172___mcc_h52;
          bool _4299_isDatatype = _4171___mcc_h51;
          bool _4300_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4301_field = _4169___mcc_h49;
          DAST._IExpression _4302_on = _4168___mcc_h48;
          {
            if (_4299_isDatatype) {
              RAST._IExpr _4303_onExpr;
              DCOMP._IOwnership _4304_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4305_recIdents;
              RAST._IExpr _out1560;
              DCOMP._IOwnership _out1561;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1562;
              (this).GenExpr(_4302_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1560, out _out1561, out _out1562);
              _4303_onExpr = _out1560;
              _4304_onOwned = _out1561;
              _4305_recIdents = _out1562;
              r = ((_4303_onExpr).Sel(DCOMP.__default.escapeName(_4301_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4306_typ;
              RAST._IType _out1563;
              _out1563 = (this).GenType(_4298_fieldType, false, false);
              _4306_typ = _out1563;
              if (((_4306_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1564;
                DCOMP._IOwnership _out1565;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1564, out _out1565);
                r = _out1564;
                resultingOwnership = _out1565;
              }
              readIdents = _4305_recIdents;
            } else {
              RAST._IExpr _4307_onExpr;
              DCOMP._IOwnership _4308_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4309_recIdents;
              RAST._IExpr _out1566;
              DCOMP._IOwnership _out1567;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1568;
              (this).GenExpr(_4302_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1566, out _out1567, out _out1568);
              _4307_onExpr = _out1566;
              _4308_onOwned = _out1567;
              _4309_recIdents = _out1568;
              r = _4307_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4301_field));
              if (_4300_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4310_s;
                _4310_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4307_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4301_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4310_s);
              }
              DCOMP._IOwnership _4311_fromOwnership;
              _4311_fromOwnership = ((_4300_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1569;
              DCOMP._IOwnership _out1570;
              DCOMP.COMP.FromOwnership(r, _4311_fromOwnership, expectedOwnership, out _out1569, out _out1570);
              r = _out1569;
              resultingOwnership = _out1570;
              readIdents = _4309_recIdents;
            }
            return ;
          }
        } else if (_source178.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _4312___mcc_h91 = _source178.dtor_elements;
          DAST._IType _4313___mcc_h92 = _source178.dtor_typ;
          DAST._IType _4314_fieldType = _4172___mcc_h52;
          bool _4315_isDatatype = _4171___mcc_h51;
          bool _4316_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4317_field = _4169___mcc_h49;
          DAST._IExpression _4318_on = _4168___mcc_h48;
          {
            if (_4315_isDatatype) {
              RAST._IExpr _4319_onExpr;
              DCOMP._IOwnership _4320_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4321_recIdents;
              RAST._IExpr _out1571;
              DCOMP._IOwnership _out1572;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1573;
              (this).GenExpr(_4318_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1571, out _out1572, out _out1573);
              _4319_onExpr = _out1571;
              _4320_onOwned = _out1572;
              _4321_recIdents = _out1573;
              r = ((_4319_onExpr).Sel(DCOMP.__default.escapeName(_4317_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4322_typ;
              RAST._IType _out1574;
              _out1574 = (this).GenType(_4314_fieldType, false, false);
              _4322_typ = _out1574;
              if (((_4322_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1575;
                DCOMP._IOwnership _out1576;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1575, out _out1576);
                r = _out1575;
                resultingOwnership = _out1576;
              }
              readIdents = _4321_recIdents;
            } else {
              RAST._IExpr _4323_onExpr;
              DCOMP._IOwnership _4324_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4325_recIdents;
              RAST._IExpr _out1577;
              DCOMP._IOwnership _out1578;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1579;
              (this).GenExpr(_4318_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1577, out _out1578, out _out1579);
              _4323_onExpr = _out1577;
              _4324_onOwned = _out1578;
              _4325_recIdents = _out1579;
              r = _4323_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4317_field));
              if (_4316_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4326_s;
                _4326_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4323_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4317_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4326_s);
              }
              DCOMP._IOwnership _4327_fromOwnership;
              _4327_fromOwnership = ((_4316_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1580;
              DCOMP._IOwnership _out1581;
              DCOMP.COMP.FromOwnership(r, _4327_fromOwnership, expectedOwnership, out _out1580, out _out1581);
              r = _out1580;
              resultingOwnership = _out1581;
              readIdents = _4325_recIdents;
            }
            return ;
          }
        } else if (_source178.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _4328___mcc_h95 = _source178.dtor_elements;
          DAST._IType _4329_fieldType = _4172___mcc_h52;
          bool _4330_isDatatype = _4171___mcc_h51;
          bool _4331_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4332_field = _4169___mcc_h49;
          DAST._IExpression _4333_on = _4168___mcc_h48;
          {
            if (_4330_isDatatype) {
              RAST._IExpr _4334_onExpr;
              DCOMP._IOwnership _4335_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4336_recIdents;
              RAST._IExpr _out1582;
              DCOMP._IOwnership _out1583;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1584;
              (this).GenExpr(_4333_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1582, out _out1583, out _out1584);
              _4334_onExpr = _out1582;
              _4335_onOwned = _out1583;
              _4336_recIdents = _out1584;
              r = ((_4334_onExpr).Sel(DCOMP.__default.escapeName(_4332_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4337_typ;
              RAST._IType _out1585;
              _out1585 = (this).GenType(_4329_fieldType, false, false);
              _4337_typ = _out1585;
              if (((_4337_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1586;
                DCOMP._IOwnership _out1587;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1586, out _out1587);
                r = _out1586;
                resultingOwnership = _out1587;
              }
              readIdents = _4336_recIdents;
            } else {
              RAST._IExpr _4338_onExpr;
              DCOMP._IOwnership _4339_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4340_recIdents;
              RAST._IExpr _out1588;
              DCOMP._IOwnership _out1589;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1590;
              (this).GenExpr(_4333_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1588, out _out1589, out _out1590);
              _4338_onExpr = _out1588;
              _4339_onOwned = _out1589;
              _4340_recIdents = _out1590;
              r = _4338_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4332_field));
              if (_4331_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4341_s;
                _4341_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4338_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4332_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4341_s);
              }
              DCOMP._IOwnership _4342_fromOwnership;
              _4342_fromOwnership = ((_4331_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1591;
              DCOMP._IOwnership _out1592;
              DCOMP.COMP.FromOwnership(r, _4342_fromOwnership, expectedOwnership, out _out1591, out _out1592);
              r = _out1591;
              resultingOwnership = _out1592;
              readIdents = _4340_recIdents;
            }
            return ;
          }
        } else if (_source178.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _4343___mcc_h97 = _source178.dtor_elements;
          DAST._IType _4344_fieldType = _4172___mcc_h52;
          bool _4345_isDatatype = _4171___mcc_h51;
          bool _4346_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4347_field = _4169___mcc_h49;
          DAST._IExpression _4348_on = _4168___mcc_h48;
          {
            if (_4345_isDatatype) {
              RAST._IExpr _4349_onExpr;
              DCOMP._IOwnership _4350_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4351_recIdents;
              RAST._IExpr _out1593;
              DCOMP._IOwnership _out1594;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1595;
              (this).GenExpr(_4348_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1593, out _out1594, out _out1595);
              _4349_onExpr = _out1593;
              _4350_onOwned = _out1594;
              _4351_recIdents = _out1595;
              r = ((_4349_onExpr).Sel(DCOMP.__default.escapeName(_4347_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4352_typ;
              RAST._IType _out1596;
              _out1596 = (this).GenType(_4344_fieldType, false, false);
              _4352_typ = _out1596;
              if (((_4352_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1597;
                DCOMP._IOwnership _out1598;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1597, out _out1598);
                r = _out1597;
                resultingOwnership = _out1598;
              }
              readIdents = _4351_recIdents;
            } else {
              RAST._IExpr _4353_onExpr;
              DCOMP._IOwnership _4354_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4355_recIdents;
              RAST._IExpr _out1599;
              DCOMP._IOwnership _out1600;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1601;
              (this).GenExpr(_4348_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1599, out _out1600, out _out1601);
              _4353_onExpr = _out1599;
              _4354_onOwned = _out1600;
              _4355_recIdents = _out1601;
              r = _4353_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4347_field));
              if (_4346_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4356_s;
                _4356_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4353_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4347_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4356_s);
              }
              DCOMP._IOwnership _4357_fromOwnership;
              _4357_fromOwnership = ((_4346_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1602;
              DCOMP._IOwnership _out1603;
              DCOMP.COMP.FromOwnership(r, _4357_fromOwnership, expectedOwnership, out _out1602, out _out1603);
              r = _out1602;
              resultingOwnership = _out1603;
              readIdents = _4355_recIdents;
            }
            return ;
          }
        } else if (_source178.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _4358___mcc_h99 = _source178.dtor_mapElems;
          DAST._IType _4359_fieldType = _4172___mcc_h52;
          bool _4360_isDatatype = _4171___mcc_h51;
          bool _4361_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4362_field = _4169___mcc_h49;
          DAST._IExpression _4363_on = _4168___mcc_h48;
          {
            if (_4360_isDatatype) {
              RAST._IExpr _4364_onExpr;
              DCOMP._IOwnership _4365_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4366_recIdents;
              RAST._IExpr _out1604;
              DCOMP._IOwnership _out1605;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1606;
              (this).GenExpr(_4363_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1604, out _out1605, out _out1606);
              _4364_onExpr = _out1604;
              _4365_onOwned = _out1605;
              _4366_recIdents = _out1606;
              r = ((_4364_onExpr).Sel(DCOMP.__default.escapeName(_4362_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4367_typ;
              RAST._IType _out1607;
              _out1607 = (this).GenType(_4359_fieldType, false, false);
              _4367_typ = _out1607;
              if (((_4367_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1608;
                DCOMP._IOwnership _out1609;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1608, out _out1609);
                r = _out1608;
                resultingOwnership = _out1609;
              }
              readIdents = _4366_recIdents;
            } else {
              RAST._IExpr _4368_onExpr;
              DCOMP._IOwnership _4369_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4370_recIdents;
              RAST._IExpr _out1610;
              DCOMP._IOwnership _out1611;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1612;
              (this).GenExpr(_4363_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1610, out _out1611, out _out1612);
              _4368_onExpr = _out1610;
              _4369_onOwned = _out1611;
              _4370_recIdents = _out1612;
              r = _4368_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4362_field));
              if (_4361_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4371_s;
                _4371_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4368_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4362_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4371_s);
              }
              DCOMP._IOwnership _4372_fromOwnership;
              _4372_fromOwnership = ((_4361_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1613;
              DCOMP._IOwnership _out1614;
              DCOMP.COMP.FromOwnership(r, _4372_fromOwnership, expectedOwnership, out _out1613, out _out1614);
              r = _out1613;
              resultingOwnership = _out1614;
              readIdents = _4370_recIdents;
            }
            return ;
          }
        } else if (_source178.is_MapBuilder) {
          DAST._IType _4373___mcc_h101 = _source178.dtor_keyType;
          DAST._IType _4374___mcc_h102 = _source178.dtor_valueType;
          DAST._IType _4375_fieldType = _4172___mcc_h52;
          bool _4376_isDatatype = _4171___mcc_h51;
          bool _4377_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4378_field = _4169___mcc_h49;
          DAST._IExpression _4379_on = _4168___mcc_h48;
          {
            if (_4376_isDatatype) {
              RAST._IExpr _4380_onExpr;
              DCOMP._IOwnership _4381_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4382_recIdents;
              RAST._IExpr _out1615;
              DCOMP._IOwnership _out1616;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1617;
              (this).GenExpr(_4379_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1615, out _out1616, out _out1617);
              _4380_onExpr = _out1615;
              _4381_onOwned = _out1616;
              _4382_recIdents = _out1617;
              r = ((_4380_onExpr).Sel(DCOMP.__default.escapeName(_4378_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4383_typ;
              RAST._IType _out1618;
              _out1618 = (this).GenType(_4375_fieldType, false, false);
              _4383_typ = _out1618;
              if (((_4383_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1619;
                DCOMP._IOwnership _out1620;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1619, out _out1620);
                r = _out1619;
                resultingOwnership = _out1620;
              }
              readIdents = _4382_recIdents;
            } else {
              RAST._IExpr _4384_onExpr;
              DCOMP._IOwnership _4385_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4386_recIdents;
              RAST._IExpr _out1621;
              DCOMP._IOwnership _out1622;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1623;
              (this).GenExpr(_4379_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1621, out _out1622, out _out1623);
              _4384_onExpr = _out1621;
              _4385_onOwned = _out1622;
              _4386_recIdents = _out1623;
              r = _4384_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4378_field));
              if (_4377_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4387_s;
                _4387_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4384_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4378_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4387_s);
              }
              DCOMP._IOwnership _4388_fromOwnership;
              _4388_fromOwnership = ((_4377_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1624;
              DCOMP._IOwnership _out1625;
              DCOMP.COMP.FromOwnership(r, _4388_fromOwnership, expectedOwnership, out _out1624, out _out1625);
              r = _out1624;
              resultingOwnership = _out1625;
              readIdents = _4386_recIdents;
            }
            return ;
          }
        } else if (_source178.is_SeqUpdate) {
          DAST._IExpression _4389___mcc_h105 = _source178.dtor_expr;
          DAST._IExpression _4390___mcc_h106 = _source178.dtor_indexExpr;
          DAST._IExpression _4391___mcc_h107 = _source178.dtor_value;
          DAST._IType _4392_fieldType = _4172___mcc_h52;
          bool _4393_isDatatype = _4171___mcc_h51;
          bool _4394_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4395_field = _4169___mcc_h49;
          DAST._IExpression _4396_on = _4168___mcc_h48;
          {
            if (_4393_isDatatype) {
              RAST._IExpr _4397_onExpr;
              DCOMP._IOwnership _4398_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4399_recIdents;
              RAST._IExpr _out1626;
              DCOMP._IOwnership _out1627;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1628;
              (this).GenExpr(_4396_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1626, out _out1627, out _out1628);
              _4397_onExpr = _out1626;
              _4398_onOwned = _out1627;
              _4399_recIdents = _out1628;
              r = ((_4397_onExpr).Sel(DCOMP.__default.escapeName(_4395_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4400_typ;
              RAST._IType _out1629;
              _out1629 = (this).GenType(_4392_fieldType, false, false);
              _4400_typ = _out1629;
              if (((_4400_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1630;
                DCOMP._IOwnership _out1631;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1630, out _out1631);
                r = _out1630;
                resultingOwnership = _out1631;
              }
              readIdents = _4399_recIdents;
            } else {
              RAST._IExpr _4401_onExpr;
              DCOMP._IOwnership _4402_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4403_recIdents;
              RAST._IExpr _out1632;
              DCOMP._IOwnership _out1633;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1634;
              (this).GenExpr(_4396_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1632, out _out1633, out _out1634);
              _4401_onExpr = _out1632;
              _4402_onOwned = _out1633;
              _4403_recIdents = _out1634;
              r = _4401_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4395_field));
              if (_4394_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4404_s;
                _4404_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4401_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4395_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4404_s);
              }
              DCOMP._IOwnership _4405_fromOwnership;
              _4405_fromOwnership = ((_4394_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1635;
              DCOMP._IOwnership _out1636;
              DCOMP.COMP.FromOwnership(r, _4405_fromOwnership, expectedOwnership, out _out1635, out _out1636);
              r = _out1635;
              resultingOwnership = _out1636;
              readIdents = _4403_recIdents;
            }
            return ;
          }
        } else if (_source178.is_MapUpdate) {
          DAST._IExpression _4406___mcc_h111 = _source178.dtor_expr;
          DAST._IExpression _4407___mcc_h112 = _source178.dtor_indexExpr;
          DAST._IExpression _4408___mcc_h113 = _source178.dtor_value;
          DAST._IType _4409_fieldType = _4172___mcc_h52;
          bool _4410_isDatatype = _4171___mcc_h51;
          bool _4411_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4412_field = _4169___mcc_h49;
          DAST._IExpression _4413_on = _4168___mcc_h48;
          {
            if (_4410_isDatatype) {
              RAST._IExpr _4414_onExpr;
              DCOMP._IOwnership _4415_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4416_recIdents;
              RAST._IExpr _out1637;
              DCOMP._IOwnership _out1638;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1639;
              (this).GenExpr(_4413_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1637, out _out1638, out _out1639);
              _4414_onExpr = _out1637;
              _4415_onOwned = _out1638;
              _4416_recIdents = _out1639;
              r = ((_4414_onExpr).Sel(DCOMP.__default.escapeName(_4412_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4417_typ;
              RAST._IType _out1640;
              _out1640 = (this).GenType(_4409_fieldType, false, false);
              _4417_typ = _out1640;
              if (((_4417_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1641;
                DCOMP._IOwnership _out1642;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1641, out _out1642);
                r = _out1641;
                resultingOwnership = _out1642;
              }
              readIdents = _4416_recIdents;
            } else {
              RAST._IExpr _4418_onExpr;
              DCOMP._IOwnership _4419_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4420_recIdents;
              RAST._IExpr _out1643;
              DCOMP._IOwnership _out1644;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1645;
              (this).GenExpr(_4413_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1643, out _out1644, out _out1645);
              _4418_onExpr = _out1643;
              _4419_onOwned = _out1644;
              _4420_recIdents = _out1645;
              r = _4418_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4412_field));
              if (_4411_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4421_s;
                _4421_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4418_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4412_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4421_s);
              }
              DCOMP._IOwnership _4422_fromOwnership;
              _4422_fromOwnership = ((_4411_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1646;
              DCOMP._IOwnership _out1647;
              DCOMP.COMP.FromOwnership(r, _4422_fromOwnership, expectedOwnership, out _out1646, out _out1647);
              r = _out1646;
              resultingOwnership = _out1647;
              readIdents = _4420_recIdents;
            }
            return ;
          }
        } else if (_source178.is_SetBuilder) {
          DAST._IType _4423___mcc_h117 = _source178.dtor_elemType;
          DAST._IType _4424_fieldType = _4172___mcc_h52;
          bool _4425_isDatatype = _4171___mcc_h51;
          bool _4426_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4427_field = _4169___mcc_h49;
          DAST._IExpression _4428_on = _4168___mcc_h48;
          {
            if (_4425_isDatatype) {
              RAST._IExpr _4429_onExpr;
              DCOMP._IOwnership _4430_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4431_recIdents;
              RAST._IExpr _out1648;
              DCOMP._IOwnership _out1649;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1650;
              (this).GenExpr(_4428_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1648, out _out1649, out _out1650);
              _4429_onExpr = _out1648;
              _4430_onOwned = _out1649;
              _4431_recIdents = _out1650;
              r = ((_4429_onExpr).Sel(DCOMP.__default.escapeName(_4427_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4432_typ;
              RAST._IType _out1651;
              _out1651 = (this).GenType(_4424_fieldType, false, false);
              _4432_typ = _out1651;
              if (((_4432_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1652;
                DCOMP._IOwnership _out1653;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1652, out _out1653);
                r = _out1652;
                resultingOwnership = _out1653;
              }
              readIdents = _4431_recIdents;
            } else {
              RAST._IExpr _4433_onExpr;
              DCOMP._IOwnership _4434_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4435_recIdents;
              RAST._IExpr _out1654;
              DCOMP._IOwnership _out1655;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1656;
              (this).GenExpr(_4428_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1654, out _out1655, out _out1656);
              _4433_onExpr = _out1654;
              _4434_onOwned = _out1655;
              _4435_recIdents = _out1656;
              r = _4433_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4427_field));
              if (_4426_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4436_s;
                _4436_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4433_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4427_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4436_s);
              }
              DCOMP._IOwnership _4437_fromOwnership;
              _4437_fromOwnership = ((_4426_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1657;
              DCOMP._IOwnership _out1658;
              DCOMP.COMP.FromOwnership(r, _4437_fromOwnership, expectedOwnership, out _out1657, out _out1658);
              r = _out1657;
              resultingOwnership = _out1658;
              readIdents = _4435_recIdents;
            }
            return ;
          }
        } else if (_source178.is_ToMultiset) {
          DAST._IExpression _4438___mcc_h119 = _source178.dtor_ToMultiset_i_a0;
          DAST._IType _4439_fieldType = _4172___mcc_h52;
          bool _4440_isDatatype = _4171___mcc_h51;
          bool _4441_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4442_field = _4169___mcc_h49;
          DAST._IExpression _4443_on = _4168___mcc_h48;
          {
            if (_4440_isDatatype) {
              RAST._IExpr _4444_onExpr;
              DCOMP._IOwnership _4445_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4446_recIdents;
              RAST._IExpr _out1659;
              DCOMP._IOwnership _out1660;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1661;
              (this).GenExpr(_4443_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1659, out _out1660, out _out1661);
              _4444_onExpr = _out1659;
              _4445_onOwned = _out1660;
              _4446_recIdents = _out1661;
              r = ((_4444_onExpr).Sel(DCOMP.__default.escapeName(_4442_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4447_typ;
              RAST._IType _out1662;
              _out1662 = (this).GenType(_4439_fieldType, false, false);
              _4447_typ = _out1662;
              if (((_4447_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1663;
                DCOMP._IOwnership _out1664;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1663, out _out1664);
                r = _out1663;
                resultingOwnership = _out1664;
              }
              readIdents = _4446_recIdents;
            } else {
              RAST._IExpr _4448_onExpr;
              DCOMP._IOwnership _4449_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4450_recIdents;
              RAST._IExpr _out1665;
              DCOMP._IOwnership _out1666;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1667;
              (this).GenExpr(_4443_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1665, out _out1666, out _out1667);
              _4448_onExpr = _out1665;
              _4449_onOwned = _out1666;
              _4450_recIdents = _out1667;
              r = _4448_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4442_field));
              if (_4441_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4451_s;
                _4451_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4448_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4442_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4451_s);
              }
              DCOMP._IOwnership _4452_fromOwnership;
              _4452_fromOwnership = ((_4441_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1668;
              DCOMP._IOwnership _out1669;
              DCOMP.COMP.FromOwnership(r, _4452_fromOwnership, expectedOwnership, out _out1668, out _out1669);
              r = _out1668;
              resultingOwnership = _out1669;
              readIdents = _4450_recIdents;
            }
            return ;
          }
        } else if (_source178.is_This) {
          DAST._IType _4453_fieldType = _4172___mcc_h52;
          bool _4454_isDatatype = _4171___mcc_h51;
          bool _4455_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4456_field = _4169___mcc_h49;
          DAST._IExpression _4457_on = _4168___mcc_h48;
          {
            if (_4454_isDatatype) {
              RAST._IExpr _4458_onExpr;
              DCOMP._IOwnership _4459_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4460_recIdents;
              RAST._IExpr _out1670;
              DCOMP._IOwnership _out1671;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1672;
              (this).GenExpr(_4457_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1670, out _out1671, out _out1672);
              _4458_onExpr = _out1670;
              _4459_onOwned = _out1671;
              _4460_recIdents = _out1672;
              r = ((_4458_onExpr).Sel(DCOMP.__default.escapeName(_4456_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4461_typ;
              RAST._IType _out1673;
              _out1673 = (this).GenType(_4453_fieldType, false, false);
              _4461_typ = _out1673;
              if (((_4461_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1674;
                DCOMP._IOwnership _out1675;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1674, out _out1675);
                r = _out1674;
                resultingOwnership = _out1675;
              }
              readIdents = _4460_recIdents;
            } else {
              RAST._IExpr _4462_onExpr;
              DCOMP._IOwnership _4463_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4464_recIdents;
              RAST._IExpr _out1676;
              DCOMP._IOwnership _out1677;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1678;
              (this).GenExpr(_4457_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1676, out _out1677, out _out1678);
              _4462_onExpr = _out1676;
              _4463_onOwned = _out1677;
              _4464_recIdents = _out1678;
              r = _4462_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4456_field));
              if (_4455_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4465_s;
                _4465_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4462_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4456_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4465_s);
              }
              DCOMP._IOwnership _4466_fromOwnership;
              _4466_fromOwnership = ((_4455_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1679;
              DCOMP._IOwnership _out1680;
              DCOMP.COMP.FromOwnership(r, _4466_fromOwnership, expectedOwnership, out _out1679, out _out1680);
              r = _out1679;
              resultingOwnership = _out1680;
              readIdents = _4464_recIdents;
            }
            return ;
          }
        } else if (_source178.is_Ite) {
          DAST._IExpression _4467___mcc_h121 = _source178.dtor_cond;
          DAST._IExpression _4468___mcc_h122 = _source178.dtor_thn;
          DAST._IExpression _4469___mcc_h123 = _source178.dtor_els;
          DAST._IType _4470_fieldType = _4172___mcc_h52;
          bool _4471_isDatatype = _4171___mcc_h51;
          bool _4472_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4473_field = _4169___mcc_h49;
          DAST._IExpression _4474_on = _4168___mcc_h48;
          {
            if (_4471_isDatatype) {
              RAST._IExpr _4475_onExpr;
              DCOMP._IOwnership _4476_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4477_recIdents;
              RAST._IExpr _out1681;
              DCOMP._IOwnership _out1682;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1683;
              (this).GenExpr(_4474_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1681, out _out1682, out _out1683);
              _4475_onExpr = _out1681;
              _4476_onOwned = _out1682;
              _4477_recIdents = _out1683;
              r = ((_4475_onExpr).Sel(DCOMP.__default.escapeName(_4473_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4478_typ;
              RAST._IType _out1684;
              _out1684 = (this).GenType(_4470_fieldType, false, false);
              _4478_typ = _out1684;
              if (((_4478_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1685;
                DCOMP._IOwnership _out1686;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1685, out _out1686);
                r = _out1685;
                resultingOwnership = _out1686;
              }
              readIdents = _4477_recIdents;
            } else {
              RAST._IExpr _4479_onExpr;
              DCOMP._IOwnership _4480_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4481_recIdents;
              RAST._IExpr _out1687;
              DCOMP._IOwnership _out1688;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1689;
              (this).GenExpr(_4474_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1687, out _out1688, out _out1689);
              _4479_onExpr = _out1687;
              _4480_onOwned = _out1688;
              _4481_recIdents = _out1689;
              r = _4479_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4473_field));
              if (_4472_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4482_s;
                _4482_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4479_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4473_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4482_s);
              }
              DCOMP._IOwnership _4483_fromOwnership;
              _4483_fromOwnership = ((_4472_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1690;
              DCOMP._IOwnership _out1691;
              DCOMP.COMP.FromOwnership(r, _4483_fromOwnership, expectedOwnership, out _out1690, out _out1691);
              r = _out1690;
              resultingOwnership = _out1691;
              readIdents = _4481_recIdents;
            }
            return ;
          }
        } else if (_source178.is_UnOp) {
          DAST._IUnaryOp _4484___mcc_h127 = _source178.dtor_unOp;
          DAST._IExpression _4485___mcc_h128 = _source178.dtor_expr;
          DAST.Format._IUnaryOpFormat _4486___mcc_h129 = _source178.dtor_format1;
          DAST._IType _4487_fieldType = _4172___mcc_h52;
          bool _4488_isDatatype = _4171___mcc_h51;
          bool _4489_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4490_field = _4169___mcc_h49;
          DAST._IExpression _4491_on = _4168___mcc_h48;
          {
            if (_4488_isDatatype) {
              RAST._IExpr _4492_onExpr;
              DCOMP._IOwnership _4493_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4494_recIdents;
              RAST._IExpr _out1692;
              DCOMP._IOwnership _out1693;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1694;
              (this).GenExpr(_4491_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1692, out _out1693, out _out1694);
              _4492_onExpr = _out1692;
              _4493_onOwned = _out1693;
              _4494_recIdents = _out1694;
              r = ((_4492_onExpr).Sel(DCOMP.__default.escapeName(_4490_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4495_typ;
              RAST._IType _out1695;
              _out1695 = (this).GenType(_4487_fieldType, false, false);
              _4495_typ = _out1695;
              if (((_4495_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1696;
                DCOMP._IOwnership _out1697;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1696, out _out1697);
                r = _out1696;
                resultingOwnership = _out1697;
              }
              readIdents = _4494_recIdents;
            } else {
              RAST._IExpr _4496_onExpr;
              DCOMP._IOwnership _4497_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4498_recIdents;
              RAST._IExpr _out1698;
              DCOMP._IOwnership _out1699;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1700;
              (this).GenExpr(_4491_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1698, out _out1699, out _out1700);
              _4496_onExpr = _out1698;
              _4497_onOwned = _out1699;
              _4498_recIdents = _out1700;
              r = _4496_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4490_field));
              if (_4489_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4499_s;
                _4499_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4496_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4490_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4499_s);
              }
              DCOMP._IOwnership _4500_fromOwnership;
              _4500_fromOwnership = ((_4489_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1701;
              DCOMP._IOwnership _out1702;
              DCOMP.COMP.FromOwnership(r, _4500_fromOwnership, expectedOwnership, out _out1701, out _out1702);
              r = _out1701;
              resultingOwnership = _out1702;
              readIdents = _4498_recIdents;
            }
            return ;
          }
        } else if (_source178.is_BinOp) {
          DAST._IBinOp _4501___mcc_h133 = _source178.dtor_op;
          DAST._IExpression _4502___mcc_h134 = _source178.dtor_left;
          DAST._IExpression _4503___mcc_h135 = _source178.dtor_right;
          DAST.Format._IBinaryOpFormat _4504___mcc_h136 = _source178.dtor_format2;
          DAST._IType _4505_fieldType = _4172___mcc_h52;
          bool _4506_isDatatype = _4171___mcc_h51;
          bool _4507_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4508_field = _4169___mcc_h49;
          DAST._IExpression _4509_on = _4168___mcc_h48;
          {
            if (_4506_isDatatype) {
              RAST._IExpr _4510_onExpr;
              DCOMP._IOwnership _4511_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4512_recIdents;
              RAST._IExpr _out1703;
              DCOMP._IOwnership _out1704;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1705;
              (this).GenExpr(_4509_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1703, out _out1704, out _out1705);
              _4510_onExpr = _out1703;
              _4511_onOwned = _out1704;
              _4512_recIdents = _out1705;
              r = ((_4510_onExpr).Sel(DCOMP.__default.escapeName(_4508_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4513_typ;
              RAST._IType _out1706;
              _out1706 = (this).GenType(_4505_fieldType, false, false);
              _4513_typ = _out1706;
              if (((_4513_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1707;
                DCOMP._IOwnership _out1708;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1707, out _out1708);
                r = _out1707;
                resultingOwnership = _out1708;
              }
              readIdents = _4512_recIdents;
            } else {
              RAST._IExpr _4514_onExpr;
              DCOMP._IOwnership _4515_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4516_recIdents;
              RAST._IExpr _out1709;
              DCOMP._IOwnership _out1710;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1711;
              (this).GenExpr(_4509_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1709, out _out1710, out _out1711);
              _4514_onExpr = _out1709;
              _4515_onOwned = _out1710;
              _4516_recIdents = _out1711;
              r = _4514_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4508_field));
              if (_4507_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4517_s;
                _4517_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4514_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4508_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4517_s);
              }
              DCOMP._IOwnership _4518_fromOwnership;
              _4518_fromOwnership = ((_4507_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1712;
              DCOMP._IOwnership _out1713;
              DCOMP.COMP.FromOwnership(r, _4518_fromOwnership, expectedOwnership, out _out1712, out _out1713);
              r = _out1712;
              resultingOwnership = _out1713;
              readIdents = _4516_recIdents;
            }
            return ;
          }
        } else if (_source178.is_ArrayLen) {
          DAST._IExpression _4519___mcc_h141 = _source178.dtor_expr;
          BigInteger _4520___mcc_h142 = _source178.dtor_dim;
          DAST._IType _4521_fieldType = _4172___mcc_h52;
          bool _4522_isDatatype = _4171___mcc_h51;
          bool _4523_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4524_field = _4169___mcc_h49;
          DAST._IExpression _4525_on = _4168___mcc_h48;
          {
            if (_4522_isDatatype) {
              RAST._IExpr _4526_onExpr;
              DCOMP._IOwnership _4527_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4528_recIdents;
              RAST._IExpr _out1714;
              DCOMP._IOwnership _out1715;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1716;
              (this).GenExpr(_4525_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1714, out _out1715, out _out1716);
              _4526_onExpr = _out1714;
              _4527_onOwned = _out1715;
              _4528_recIdents = _out1716;
              r = ((_4526_onExpr).Sel(DCOMP.__default.escapeName(_4524_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4529_typ;
              RAST._IType _out1717;
              _out1717 = (this).GenType(_4521_fieldType, false, false);
              _4529_typ = _out1717;
              if (((_4529_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1718;
                DCOMP._IOwnership _out1719;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1718, out _out1719);
                r = _out1718;
                resultingOwnership = _out1719;
              }
              readIdents = _4528_recIdents;
            } else {
              RAST._IExpr _4530_onExpr;
              DCOMP._IOwnership _4531_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4532_recIdents;
              RAST._IExpr _out1720;
              DCOMP._IOwnership _out1721;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1722;
              (this).GenExpr(_4525_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1720, out _out1721, out _out1722);
              _4530_onExpr = _out1720;
              _4531_onOwned = _out1721;
              _4532_recIdents = _out1722;
              r = _4530_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4524_field));
              if (_4523_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4533_s;
                _4533_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4530_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4524_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4533_s);
              }
              DCOMP._IOwnership _4534_fromOwnership;
              _4534_fromOwnership = ((_4523_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1723;
              DCOMP._IOwnership _out1724;
              DCOMP.COMP.FromOwnership(r, _4534_fromOwnership, expectedOwnership, out _out1723, out _out1724);
              r = _out1723;
              resultingOwnership = _out1724;
              readIdents = _4532_recIdents;
            }
            return ;
          }
        } else if (_source178.is_MapKeys) {
          DAST._IExpression _4535___mcc_h145 = _source178.dtor_expr;
          DAST._IType _4536_fieldType = _4172___mcc_h52;
          bool _4537_isDatatype = _4171___mcc_h51;
          bool _4538_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4539_field = _4169___mcc_h49;
          DAST._IExpression _4540_on = _4168___mcc_h48;
          {
            if (_4537_isDatatype) {
              RAST._IExpr _4541_onExpr;
              DCOMP._IOwnership _4542_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4543_recIdents;
              RAST._IExpr _out1725;
              DCOMP._IOwnership _out1726;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1727;
              (this).GenExpr(_4540_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1725, out _out1726, out _out1727);
              _4541_onExpr = _out1725;
              _4542_onOwned = _out1726;
              _4543_recIdents = _out1727;
              r = ((_4541_onExpr).Sel(DCOMP.__default.escapeName(_4539_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4544_typ;
              RAST._IType _out1728;
              _out1728 = (this).GenType(_4536_fieldType, false, false);
              _4544_typ = _out1728;
              if (((_4544_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1729;
                DCOMP._IOwnership _out1730;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1729, out _out1730);
                r = _out1729;
                resultingOwnership = _out1730;
              }
              readIdents = _4543_recIdents;
            } else {
              RAST._IExpr _4545_onExpr;
              DCOMP._IOwnership _4546_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4547_recIdents;
              RAST._IExpr _out1731;
              DCOMP._IOwnership _out1732;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1733;
              (this).GenExpr(_4540_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1731, out _out1732, out _out1733);
              _4545_onExpr = _out1731;
              _4546_onOwned = _out1732;
              _4547_recIdents = _out1733;
              r = _4545_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4539_field));
              if (_4538_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4548_s;
                _4548_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4545_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4539_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4548_s);
              }
              DCOMP._IOwnership _4549_fromOwnership;
              _4549_fromOwnership = ((_4538_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1734;
              DCOMP._IOwnership _out1735;
              DCOMP.COMP.FromOwnership(r, _4549_fromOwnership, expectedOwnership, out _out1734, out _out1735);
              r = _out1734;
              resultingOwnership = _out1735;
              readIdents = _4547_recIdents;
            }
            return ;
          }
        } else if (_source178.is_MapValues) {
          DAST._IExpression _4550___mcc_h147 = _source178.dtor_expr;
          DAST._IType _4551_fieldType = _4172___mcc_h52;
          bool _4552_isDatatype = _4171___mcc_h51;
          bool _4553_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4554_field = _4169___mcc_h49;
          DAST._IExpression _4555_on = _4168___mcc_h48;
          {
            if (_4552_isDatatype) {
              RAST._IExpr _4556_onExpr;
              DCOMP._IOwnership _4557_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4558_recIdents;
              RAST._IExpr _out1736;
              DCOMP._IOwnership _out1737;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1738;
              (this).GenExpr(_4555_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1736, out _out1737, out _out1738);
              _4556_onExpr = _out1736;
              _4557_onOwned = _out1737;
              _4558_recIdents = _out1738;
              r = ((_4556_onExpr).Sel(DCOMP.__default.escapeName(_4554_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4559_typ;
              RAST._IType _out1739;
              _out1739 = (this).GenType(_4551_fieldType, false, false);
              _4559_typ = _out1739;
              if (((_4559_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1740;
                DCOMP._IOwnership _out1741;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1740, out _out1741);
                r = _out1740;
                resultingOwnership = _out1741;
              }
              readIdents = _4558_recIdents;
            } else {
              RAST._IExpr _4560_onExpr;
              DCOMP._IOwnership _4561_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4562_recIdents;
              RAST._IExpr _out1742;
              DCOMP._IOwnership _out1743;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1744;
              (this).GenExpr(_4555_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1742, out _out1743, out _out1744);
              _4560_onExpr = _out1742;
              _4561_onOwned = _out1743;
              _4562_recIdents = _out1744;
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
              RAST._IExpr _out1745;
              DCOMP._IOwnership _out1746;
              DCOMP.COMP.FromOwnership(r, _4564_fromOwnership, expectedOwnership, out _out1745, out _out1746);
              r = _out1745;
              resultingOwnership = _out1746;
              readIdents = _4562_recIdents;
            }
            return ;
          }
        } else if (_source178.is_Select) {
          DAST._IExpression _4565___mcc_h149 = _source178.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _4566___mcc_h150 = _source178.dtor_field;
          bool _4567___mcc_h151 = _source178.dtor_isConstant;
          bool _4568___mcc_h152 = _source178.dtor_onDatatype;
          DAST._IType _4569___mcc_h153 = _source178.dtor_fieldType;
          DAST._IType _4570_fieldType = _4172___mcc_h52;
          bool _4571_isDatatype = _4171___mcc_h51;
          bool _4572_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4573_field = _4169___mcc_h49;
          DAST._IExpression _4574_on = _4168___mcc_h48;
          {
            if (_4571_isDatatype) {
              RAST._IExpr _4575_onExpr;
              DCOMP._IOwnership _4576_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4577_recIdents;
              RAST._IExpr _out1747;
              DCOMP._IOwnership _out1748;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1749;
              (this).GenExpr(_4574_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1747, out _out1748, out _out1749);
              _4575_onExpr = _out1747;
              _4576_onOwned = _out1748;
              _4577_recIdents = _out1749;
              r = ((_4575_onExpr).Sel(DCOMP.__default.escapeName(_4573_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4578_typ;
              RAST._IType _out1750;
              _out1750 = (this).GenType(_4570_fieldType, false, false);
              _4578_typ = _out1750;
              if (((_4578_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1751;
                DCOMP._IOwnership _out1752;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1751, out _out1752);
                r = _out1751;
                resultingOwnership = _out1752;
              }
              readIdents = _4577_recIdents;
            } else {
              RAST._IExpr _4579_onExpr;
              DCOMP._IOwnership _4580_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4581_recIdents;
              RAST._IExpr _out1753;
              DCOMP._IOwnership _out1754;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1755;
              (this).GenExpr(_4574_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1753, out _out1754, out _out1755);
              _4579_onExpr = _out1753;
              _4580_onOwned = _out1754;
              _4581_recIdents = _out1755;
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
              RAST._IExpr _out1756;
              DCOMP._IOwnership _out1757;
              DCOMP.COMP.FromOwnership(r, _4583_fromOwnership, expectedOwnership, out _out1756, out _out1757);
              r = _out1756;
              resultingOwnership = _out1757;
              readIdents = _4581_recIdents;
            }
            return ;
          }
        } else if (_source178.is_SelectFn) {
          DAST._IExpression _4584___mcc_h159 = _source178.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _4585___mcc_h160 = _source178.dtor_field;
          bool _4586___mcc_h161 = _source178.dtor_onDatatype;
          bool _4587___mcc_h162 = _source178.dtor_isStatic;
          BigInteger _4588___mcc_h163 = _source178.dtor_arity;
          DAST._IType _4589_fieldType = _4172___mcc_h52;
          bool _4590_isDatatype = _4171___mcc_h51;
          bool _4591_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4592_field = _4169___mcc_h49;
          DAST._IExpression _4593_on = _4168___mcc_h48;
          {
            if (_4590_isDatatype) {
              RAST._IExpr _4594_onExpr;
              DCOMP._IOwnership _4595_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4596_recIdents;
              RAST._IExpr _out1758;
              DCOMP._IOwnership _out1759;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1760;
              (this).GenExpr(_4593_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1758, out _out1759, out _out1760);
              _4594_onExpr = _out1758;
              _4595_onOwned = _out1759;
              _4596_recIdents = _out1760;
              r = ((_4594_onExpr).Sel(DCOMP.__default.escapeName(_4592_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4597_typ;
              RAST._IType _out1761;
              _out1761 = (this).GenType(_4589_fieldType, false, false);
              _4597_typ = _out1761;
              if (((_4597_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1762;
                DCOMP._IOwnership _out1763;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1762, out _out1763);
                r = _out1762;
                resultingOwnership = _out1763;
              }
              readIdents = _4596_recIdents;
            } else {
              RAST._IExpr _4598_onExpr;
              DCOMP._IOwnership _4599_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4600_recIdents;
              RAST._IExpr _out1764;
              DCOMP._IOwnership _out1765;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1766;
              (this).GenExpr(_4593_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1764, out _out1765, out _out1766);
              _4598_onExpr = _out1764;
              _4599_onOwned = _out1765;
              _4600_recIdents = _out1766;
              r = _4598_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4592_field));
              if (_4591_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4601_s;
                _4601_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4598_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4592_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4601_s);
              }
              DCOMP._IOwnership _4602_fromOwnership;
              _4602_fromOwnership = ((_4591_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1767;
              DCOMP._IOwnership _out1768;
              DCOMP.COMP.FromOwnership(r, _4602_fromOwnership, expectedOwnership, out _out1767, out _out1768);
              r = _out1767;
              resultingOwnership = _out1768;
              readIdents = _4600_recIdents;
            }
            return ;
          }
        } else if (_source178.is_Index) {
          DAST._IExpression _4603___mcc_h169 = _source178.dtor_expr;
          DAST._ICollKind _4604___mcc_h170 = _source178.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _4605___mcc_h171 = _source178.dtor_indices;
          DAST._IType _4606_fieldType = _4172___mcc_h52;
          bool _4607_isDatatype = _4171___mcc_h51;
          bool _4608_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4609_field = _4169___mcc_h49;
          DAST._IExpression _4610_on = _4168___mcc_h48;
          {
            if (_4607_isDatatype) {
              RAST._IExpr _4611_onExpr;
              DCOMP._IOwnership _4612_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4613_recIdents;
              RAST._IExpr _out1769;
              DCOMP._IOwnership _out1770;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1771;
              (this).GenExpr(_4610_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1769, out _out1770, out _out1771);
              _4611_onExpr = _out1769;
              _4612_onOwned = _out1770;
              _4613_recIdents = _out1771;
              r = ((_4611_onExpr).Sel(DCOMP.__default.escapeName(_4609_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4614_typ;
              RAST._IType _out1772;
              _out1772 = (this).GenType(_4606_fieldType, false, false);
              _4614_typ = _out1772;
              if (((_4614_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1773;
                DCOMP._IOwnership _out1774;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1773, out _out1774);
                r = _out1773;
                resultingOwnership = _out1774;
              }
              readIdents = _4613_recIdents;
            } else {
              RAST._IExpr _4615_onExpr;
              DCOMP._IOwnership _4616_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4617_recIdents;
              RAST._IExpr _out1775;
              DCOMP._IOwnership _out1776;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1777;
              (this).GenExpr(_4610_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1775, out _out1776, out _out1777);
              _4615_onExpr = _out1775;
              _4616_onOwned = _out1776;
              _4617_recIdents = _out1777;
              r = _4615_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4609_field));
              if (_4608_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4618_s;
                _4618_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4615_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4609_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4618_s);
              }
              DCOMP._IOwnership _4619_fromOwnership;
              _4619_fromOwnership = ((_4608_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1778;
              DCOMP._IOwnership _out1779;
              DCOMP.COMP.FromOwnership(r, _4619_fromOwnership, expectedOwnership, out _out1778, out _out1779);
              r = _out1778;
              resultingOwnership = _out1779;
              readIdents = _4617_recIdents;
            }
            return ;
          }
        } else if (_source178.is_IndexRange) {
          DAST._IExpression _4620___mcc_h175 = _source178.dtor_expr;
          bool _4621___mcc_h176 = _source178.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _4622___mcc_h177 = _source178.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _4623___mcc_h178 = _source178.dtor_high;
          DAST._IType _4624_fieldType = _4172___mcc_h52;
          bool _4625_isDatatype = _4171___mcc_h51;
          bool _4626_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4627_field = _4169___mcc_h49;
          DAST._IExpression _4628_on = _4168___mcc_h48;
          {
            if (_4625_isDatatype) {
              RAST._IExpr _4629_onExpr;
              DCOMP._IOwnership _4630_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4631_recIdents;
              RAST._IExpr _out1780;
              DCOMP._IOwnership _out1781;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1782;
              (this).GenExpr(_4628_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1780, out _out1781, out _out1782);
              _4629_onExpr = _out1780;
              _4630_onOwned = _out1781;
              _4631_recIdents = _out1782;
              r = ((_4629_onExpr).Sel(DCOMP.__default.escapeName(_4627_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4632_typ;
              RAST._IType _out1783;
              _out1783 = (this).GenType(_4624_fieldType, false, false);
              _4632_typ = _out1783;
              if (((_4632_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1784;
                DCOMP._IOwnership _out1785;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1784, out _out1785);
                r = _out1784;
                resultingOwnership = _out1785;
              }
              readIdents = _4631_recIdents;
            } else {
              RAST._IExpr _4633_onExpr;
              DCOMP._IOwnership _4634_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4635_recIdents;
              RAST._IExpr _out1786;
              DCOMP._IOwnership _out1787;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1788;
              (this).GenExpr(_4628_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1786, out _out1787, out _out1788);
              _4633_onExpr = _out1786;
              _4634_onOwned = _out1787;
              _4635_recIdents = _out1788;
              r = _4633_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4627_field));
              if (_4626_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4636_s;
                _4636_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4633_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4627_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4636_s);
              }
              DCOMP._IOwnership _4637_fromOwnership;
              _4637_fromOwnership = ((_4626_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1789;
              DCOMP._IOwnership _out1790;
              DCOMP.COMP.FromOwnership(r, _4637_fromOwnership, expectedOwnership, out _out1789, out _out1790);
              r = _out1789;
              resultingOwnership = _out1790;
              readIdents = _4635_recIdents;
            }
            return ;
          }
        } else if (_source178.is_TupleSelect) {
          DAST._IExpression _4638___mcc_h183 = _source178.dtor_expr;
          BigInteger _4639___mcc_h184 = _source178.dtor_index;
          DAST._IType _4640___mcc_h185 = _source178.dtor_fieldType;
          DAST._IType _4641_fieldType = _4172___mcc_h52;
          bool _4642_isDatatype = _4171___mcc_h51;
          bool _4643_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4644_field = _4169___mcc_h49;
          DAST._IExpression _4645_on = _4168___mcc_h48;
          {
            if (_4642_isDatatype) {
              RAST._IExpr _4646_onExpr;
              DCOMP._IOwnership _4647_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4648_recIdents;
              RAST._IExpr _out1791;
              DCOMP._IOwnership _out1792;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1793;
              (this).GenExpr(_4645_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1791, out _out1792, out _out1793);
              _4646_onExpr = _out1791;
              _4647_onOwned = _out1792;
              _4648_recIdents = _out1793;
              r = ((_4646_onExpr).Sel(DCOMP.__default.escapeName(_4644_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4649_typ;
              RAST._IType _out1794;
              _out1794 = (this).GenType(_4641_fieldType, false, false);
              _4649_typ = _out1794;
              if (((_4649_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1795;
                DCOMP._IOwnership _out1796;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1795, out _out1796);
                r = _out1795;
                resultingOwnership = _out1796;
              }
              readIdents = _4648_recIdents;
            } else {
              RAST._IExpr _4650_onExpr;
              DCOMP._IOwnership _4651_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4652_recIdents;
              RAST._IExpr _out1797;
              DCOMP._IOwnership _out1798;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1799;
              (this).GenExpr(_4645_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1797, out _out1798, out _out1799);
              _4650_onExpr = _out1797;
              _4651_onOwned = _out1798;
              _4652_recIdents = _out1799;
              r = _4650_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4644_field));
              if (_4643_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4653_s;
                _4653_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4650_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4644_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4653_s);
              }
              DCOMP._IOwnership _4654_fromOwnership;
              _4654_fromOwnership = ((_4643_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1800;
              DCOMP._IOwnership _out1801;
              DCOMP.COMP.FromOwnership(r, _4654_fromOwnership, expectedOwnership, out _out1800, out _out1801);
              r = _out1800;
              resultingOwnership = _out1801;
              readIdents = _4652_recIdents;
            }
            return ;
          }
        } else if (_source178.is_Call) {
          DAST._IExpression _4655___mcc_h189 = _source178.dtor_on;
          DAST._ICallName _4656___mcc_h190 = _source178.dtor_callName;
          Dafny.ISequence<DAST._IType> _4657___mcc_h191 = _source178.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _4658___mcc_h192 = _source178.dtor_args;
          DAST._IType _4659_fieldType = _4172___mcc_h52;
          bool _4660_isDatatype = _4171___mcc_h51;
          bool _4661_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4662_field = _4169___mcc_h49;
          DAST._IExpression _4663_on = _4168___mcc_h48;
          {
            if (_4660_isDatatype) {
              RAST._IExpr _4664_onExpr;
              DCOMP._IOwnership _4665_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4666_recIdents;
              RAST._IExpr _out1802;
              DCOMP._IOwnership _out1803;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1804;
              (this).GenExpr(_4663_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1802, out _out1803, out _out1804);
              _4664_onExpr = _out1802;
              _4665_onOwned = _out1803;
              _4666_recIdents = _out1804;
              r = ((_4664_onExpr).Sel(DCOMP.__default.escapeName(_4662_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4667_typ;
              RAST._IType _out1805;
              _out1805 = (this).GenType(_4659_fieldType, false, false);
              _4667_typ = _out1805;
              if (((_4667_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1806;
                DCOMP._IOwnership _out1807;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1806, out _out1807);
                r = _out1806;
                resultingOwnership = _out1807;
              }
              readIdents = _4666_recIdents;
            } else {
              RAST._IExpr _4668_onExpr;
              DCOMP._IOwnership _4669_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4670_recIdents;
              RAST._IExpr _out1808;
              DCOMP._IOwnership _out1809;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1810;
              (this).GenExpr(_4663_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1808, out _out1809, out _out1810);
              _4668_onExpr = _out1808;
              _4669_onOwned = _out1809;
              _4670_recIdents = _out1810;
              r = _4668_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4662_field));
              if (_4661_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4671_s;
                _4671_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4668_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4662_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4671_s);
              }
              DCOMP._IOwnership _4672_fromOwnership;
              _4672_fromOwnership = ((_4661_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1811;
              DCOMP._IOwnership _out1812;
              DCOMP.COMP.FromOwnership(r, _4672_fromOwnership, expectedOwnership, out _out1811, out _out1812);
              r = _out1811;
              resultingOwnership = _out1812;
              readIdents = _4670_recIdents;
            }
            return ;
          }
        } else if (_source178.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _4673___mcc_h197 = _source178.dtor_params;
          DAST._IType _4674___mcc_h198 = _source178.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _4675___mcc_h199 = _source178.dtor_body;
          DAST._IType _4676_fieldType = _4172___mcc_h52;
          bool _4677_isDatatype = _4171___mcc_h51;
          bool _4678_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4679_field = _4169___mcc_h49;
          DAST._IExpression _4680_on = _4168___mcc_h48;
          {
            if (_4677_isDatatype) {
              RAST._IExpr _4681_onExpr;
              DCOMP._IOwnership _4682_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4683_recIdents;
              RAST._IExpr _out1813;
              DCOMP._IOwnership _out1814;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1815;
              (this).GenExpr(_4680_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1813, out _out1814, out _out1815);
              _4681_onExpr = _out1813;
              _4682_onOwned = _out1814;
              _4683_recIdents = _out1815;
              r = ((_4681_onExpr).Sel(DCOMP.__default.escapeName(_4679_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4684_typ;
              RAST._IType _out1816;
              _out1816 = (this).GenType(_4676_fieldType, false, false);
              _4684_typ = _out1816;
              if (((_4684_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1817;
                DCOMP._IOwnership _out1818;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1817, out _out1818);
                r = _out1817;
                resultingOwnership = _out1818;
              }
              readIdents = _4683_recIdents;
            } else {
              RAST._IExpr _4685_onExpr;
              DCOMP._IOwnership _4686_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4687_recIdents;
              RAST._IExpr _out1819;
              DCOMP._IOwnership _out1820;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1821;
              (this).GenExpr(_4680_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1819, out _out1820, out _out1821);
              _4685_onExpr = _out1819;
              _4686_onOwned = _out1820;
              _4687_recIdents = _out1821;
              r = _4685_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4679_field));
              if (_4678_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4688_s;
                _4688_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4685_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4679_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4688_s);
              }
              DCOMP._IOwnership _4689_fromOwnership;
              _4689_fromOwnership = ((_4678_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1822;
              DCOMP._IOwnership _out1823;
              DCOMP.COMP.FromOwnership(r, _4689_fromOwnership, expectedOwnership, out _out1822, out _out1823);
              r = _out1822;
              resultingOwnership = _out1823;
              readIdents = _4687_recIdents;
            }
            return ;
          }
        } else if (_source178.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _4690___mcc_h203 = _source178.dtor_values;
          DAST._IType _4691___mcc_h204 = _source178.dtor_retType;
          DAST._IExpression _4692___mcc_h205 = _source178.dtor_expr;
          DAST._IType _4693_fieldType = _4172___mcc_h52;
          bool _4694_isDatatype = _4171___mcc_h51;
          bool _4695_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4696_field = _4169___mcc_h49;
          DAST._IExpression _4697_on = _4168___mcc_h48;
          {
            if (_4694_isDatatype) {
              RAST._IExpr _4698_onExpr;
              DCOMP._IOwnership _4699_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4700_recIdents;
              RAST._IExpr _out1824;
              DCOMP._IOwnership _out1825;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1826;
              (this).GenExpr(_4697_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1824, out _out1825, out _out1826);
              _4698_onExpr = _out1824;
              _4699_onOwned = _out1825;
              _4700_recIdents = _out1826;
              r = ((_4698_onExpr).Sel(DCOMP.__default.escapeName(_4696_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4701_typ;
              RAST._IType _out1827;
              _out1827 = (this).GenType(_4693_fieldType, false, false);
              _4701_typ = _out1827;
              if (((_4701_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1828;
                DCOMP._IOwnership _out1829;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1828, out _out1829);
                r = _out1828;
                resultingOwnership = _out1829;
              }
              readIdents = _4700_recIdents;
            } else {
              RAST._IExpr _4702_onExpr;
              DCOMP._IOwnership _4703_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4704_recIdents;
              RAST._IExpr _out1830;
              DCOMP._IOwnership _out1831;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1832;
              (this).GenExpr(_4697_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1830, out _out1831, out _out1832);
              _4702_onExpr = _out1830;
              _4703_onOwned = _out1831;
              _4704_recIdents = _out1832;
              r = _4702_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4696_field));
              if (_4695_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4705_s;
                _4705_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4702_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4696_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4705_s);
              }
              DCOMP._IOwnership _4706_fromOwnership;
              _4706_fromOwnership = ((_4695_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1833;
              DCOMP._IOwnership _out1834;
              DCOMP.COMP.FromOwnership(r, _4706_fromOwnership, expectedOwnership, out _out1833, out _out1834);
              r = _out1833;
              resultingOwnership = _out1834;
              readIdents = _4704_recIdents;
            }
            return ;
          }
        } else if (_source178.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _4707___mcc_h209 = _source178.dtor_name;
          DAST._IType _4708___mcc_h210 = _source178.dtor_typ;
          DAST._IExpression _4709___mcc_h211 = _source178.dtor_value;
          DAST._IExpression _4710___mcc_h212 = _source178.dtor_iifeBody;
          DAST._IType _4711_fieldType = _4172___mcc_h52;
          bool _4712_isDatatype = _4171___mcc_h51;
          bool _4713_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4714_field = _4169___mcc_h49;
          DAST._IExpression _4715_on = _4168___mcc_h48;
          {
            if (_4712_isDatatype) {
              RAST._IExpr _4716_onExpr;
              DCOMP._IOwnership _4717_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4718_recIdents;
              RAST._IExpr _out1835;
              DCOMP._IOwnership _out1836;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1837;
              (this).GenExpr(_4715_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1835, out _out1836, out _out1837);
              _4716_onExpr = _out1835;
              _4717_onOwned = _out1836;
              _4718_recIdents = _out1837;
              r = ((_4716_onExpr).Sel(DCOMP.__default.escapeName(_4714_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4719_typ;
              RAST._IType _out1838;
              _out1838 = (this).GenType(_4711_fieldType, false, false);
              _4719_typ = _out1838;
              if (((_4719_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1839;
                DCOMP._IOwnership _out1840;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1839, out _out1840);
                r = _out1839;
                resultingOwnership = _out1840;
              }
              readIdents = _4718_recIdents;
            } else {
              RAST._IExpr _4720_onExpr;
              DCOMP._IOwnership _4721_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4722_recIdents;
              RAST._IExpr _out1841;
              DCOMP._IOwnership _out1842;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1843;
              (this).GenExpr(_4715_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1841, out _out1842, out _out1843);
              _4720_onExpr = _out1841;
              _4721_onOwned = _out1842;
              _4722_recIdents = _out1843;
              r = _4720_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4714_field));
              if (_4713_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4723_s;
                _4723_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4720_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4714_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4723_s);
              }
              DCOMP._IOwnership _4724_fromOwnership;
              _4724_fromOwnership = ((_4713_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1844;
              DCOMP._IOwnership _out1845;
              DCOMP.COMP.FromOwnership(r, _4724_fromOwnership, expectedOwnership, out _out1844, out _out1845);
              r = _out1844;
              resultingOwnership = _out1845;
              readIdents = _4722_recIdents;
            }
            return ;
          }
        } else if (_source178.is_Apply) {
          DAST._IExpression _4725___mcc_h217 = _source178.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _4726___mcc_h218 = _source178.dtor_args;
          DAST._IType _4727_fieldType = _4172___mcc_h52;
          bool _4728_isDatatype = _4171___mcc_h51;
          bool _4729_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4730_field = _4169___mcc_h49;
          DAST._IExpression _4731_on = _4168___mcc_h48;
          {
            if (_4728_isDatatype) {
              RAST._IExpr _4732_onExpr;
              DCOMP._IOwnership _4733_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4734_recIdents;
              RAST._IExpr _out1846;
              DCOMP._IOwnership _out1847;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1848;
              (this).GenExpr(_4731_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1846, out _out1847, out _out1848);
              _4732_onExpr = _out1846;
              _4733_onOwned = _out1847;
              _4734_recIdents = _out1848;
              r = ((_4732_onExpr).Sel(DCOMP.__default.escapeName(_4730_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4735_typ;
              RAST._IType _out1849;
              _out1849 = (this).GenType(_4727_fieldType, false, false);
              _4735_typ = _out1849;
              if (((_4735_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1850;
                DCOMP._IOwnership _out1851;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1850, out _out1851);
                r = _out1850;
                resultingOwnership = _out1851;
              }
              readIdents = _4734_recIdents;
            } else {
              RAST._IExpr _4736_onExpr;
              DCOMP._IOwnership _4737_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4738_recIdents;
              RAST._IExpr _out1852;
              DCOMP._IOwnership _out1853;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1854;
              (this).GenExpr(_4731_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1852, out _out1853, out _out1854);
              _4736_onExpr = _out1852;
              _4737_onOwned = _out1853;
              _4738_recIdents = _out1854;
              r = _4736_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4730_field));
              if (_4729_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4739_s;
                _4739_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4736_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4730_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4739_s);
              }
              DCOMP._IOwnership _4740_fromOwnership;
              _4740_fromOwnership = ((_4729_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1855;
              DCOMP._IOwnership _out1856;
              DCOMP.COMP.FromOwnership(r, _4740_fromOwnership, expectedOwnership, out _out1855, out _out1856);
              r = _out1855;
              resultingOwnership = _out1856;
              readIdents = _4738_recIdents;
            }
            return ;
          }
        } else if (_source178.is_TypeTest) {
          DAST._IExpression _4741___mcc_h221 = _source178.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4742___mcc_h222 = _source178.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _4743___mcc_h223 = _source178.dtor_variant;
          DAST._IType _4744_fieldType = _4172___mcc_h52;
          bool _4745_isDatatype = _4171___mcc_h51;
          bool _4746_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4747_field = _4169___mcc_h49;
          DAST._IExpression _4748_on = _4168___mcc_h48;
          {
            if (_4745_isDatatype) {
              RAST._IExpr _4749_onExpr;
              DCOMP._IOwnership _4750_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4751_recIdents;
              RAST._IExpr _out1857;
              DCOMP._IOwnership _out1858;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1859;
              (this).GenExpr(_4748_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1857, out _out1858, out _out1859);
              _4749_onExpr = _out1857;
              _4750_onOwned = _out1858;
              _4751_recIdents = _out1859;
              r = ((_4749_onExpr).Sel(DCOMP.__default.escapeName(_4747_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4752_typ;
              RAST._IType _out1860;
              _out1860 = (this).GenType(_4744_fieldType, false, false);
              _4752_typ = _out1860;
              if (((_4752_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1861;
                DCOMP._IOwnership _out1862;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1861, out _out1862);
                r = _out1861;
                resultingOwnership = _out1862;
              }
              readIdents = _4751_recIdents;
            } else {
              RAST._IExpr _4753_onExpr;
              DCOMP._IOwnership _4754_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4755_recIdents;
              RAST._IExpr _out1863;
              DCOMP._IOwnership _out1864;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1865;
              (this).GenExpr(_4748_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1863, out _out1864, out _out1865);
              _4753_onExpr = _out1863;
              _4754_onOwned = _out1864;
              _4755_recIdents = _out1865;
              r = _4753_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4747_field));
              if (_4746_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4756_s;
                _4756_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4753_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4747_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4756_s);
              }
              DCOMP._IOwnership _4757_fromOwnership;
              _4757_fromOwnership = ((_4746_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1866;
              DCOMP._IOwnership _out1867;
              DCOMP.COMP.FromOwnership(r, _4757_fromOwnership, expectedOwnership, out _out1866, out _out1867);
              r = _out1866;
              resultingOwnership = _out1867;
              readIdents = _4755_recIdents;
            }
            return ;
          }
        } else if (_source178.is_InitializationValue) {
          DAST._IType _4758___mcc_h227 = _source178.dtor_typ;
          DAST._IType _4759_fieldType = _4172___mcc_h52;
          bool _4760_isDatatype = _4171___mcc_h51;
          bool _4761_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4762_field = _4169___mcc_h49;
          DAST._IExpression _4763_on = _4168___mcc_h48;
          {
            if (_4760_isDatatype) {
              RAST._IExpr _4764_onExpr;
              DCOMP._IOwnership _4765_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4766_recIdents;
              RAST._IExpr _out1868;
              DCOMP._IOwnership _out1869;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1870;
              (this).GenExpr(_4763_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1868, out _out1869, out _out1870);
              _4764_onExpr = _out1868;
              _4765_onOwned = _out1869;
              _4766_recIdents = _out1870;
              r = ((_4764_onExpr).Sel(DCOMP.__default.escapeName(_4762_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4767_typ;
              RAST._IType _out1871;
              _out1871 = (this).GenType(_4759_fieldType, false, false);
              _4767_typ = _out1871;
              if (((_4767_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1872;
                DCOMP._IOwnership _out1873;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1872, out _out1873);
                r = _out1872;
                resultingOwnership = _out1873;
              }
              readIdents = _4766_recIdents;
            } else {
              RAST._IExpr _4768_onExpr;
              DCOMP._IOwnership _4769_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4770_recIdents;
              RAST._IExpr _out1874;
              DCOMP._IOwnership _out1875;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1876;
              (this).GenExpr(_4763_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1874, out _out1875, out _out1876);
              _4768_onExpr = _out1874;
              _4769_onOwned = _out1875;
              _4770_recIdents = _out1876;
              r = _4768_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4762_field));
              if (_4761_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4771_s;
                _4771_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4768_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4762_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4771_s);
              }
              DCOMP._IOwnership _4772_fromOwnership;
              _4772_fromOwnership = ((_4761_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1877;
              DCOMP._IOwnership _out1878;
              DCOMP.COMP.FromOwnership(r, _4772_fromOwnership, expectedOwnership, out _out1877, out _out1878);
              r = _out1877;
              resultingOwnership = _out1878;
              readIdents = _4770_recIdents;
            }
            return ;
          }
        } else if (_source178.is_BoolBoundedPool) {
          DAST._IType _4773_fieldType = _4172___mcc_h52;
          bool _4774_isDatatype = _4171___mcc_h51;
          bool _4775_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4776_field = _4169___mcc_h49;
          DAST._IExpression _4777_on = _4168___mcc_h48;
          {
            if (_4774_isDatatype) {
              RAST._IExpr _4778_onExpr;
              DCOMP._IOwnership _4779_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4780_recIdents;
              RAST._IExpr _out1879;
              DCOMP._IOwnership _out1880;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1881;
              (this).GenExpr(_4777_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1879, out _out1880, out _out1881);
              _4778_onExpr = _out1879;
              _4779_onOwned = _out1880;
              _4780_recIdents = _out1881;
              r = ((_4778_onExpr).Sel(DCOMP.__default.escapeName(_4776_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4781_typ;
              RAST._IType _out1882;
              _out1882 = (this).GenType(_4773_fieldType, false, false);
              _4781_typ = _out1882;
              if (((_4781_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1883;
                DCOMP._IOwnership _out1884;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1883, out _out1884);
                r = _out1883;
                resultingOwnership = _out1884;
              }
              readIdents = _4780_recIdents;
            } else {
              RAST._IExpr _4782_onExpr;
              DCOMP._IOwnership _4783_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4784_recIdents;
              RAST._IExpr _out1885;
              DCOMP._IOwnership _out1886;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1887;
              (this).GenExpr(_4777_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1885, out _out1886, out _out1887);
              _4782_onExpr = _out1885;
              _4783_onOwned = _out1886;
              _4784_recIdents = _out1887;
              r = _4782_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4776_field));
              if (_4775_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4785_s;
                _4785_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4782_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4776_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4785_s);
              }
              DCOMP._IOwnership _4786_fromOwnership;
              _4786_fromOwnership = ((_4775_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1888;
              DCOMP._IOwnership _out1889;
              DCOMP.COMP.FromOwnership(r, _4786_fromOwnership, expectedOwnership, out _out1888, out _out1889);
              r = _out1888;
              resultingOwnership = _out1889;
              readIdents = _4784_recIdents;
            }
            return ;
          }
        } else if (_source178.is_SetBoundedPool) {
          DAST._IExpression _4787___mcc_h229 = _source178.dtor_of;
          DAST._IType _4788_fieldType = _4172___mcc_h52;
          bool _4789_isDatatype = _4171___mcc_h51;
          bool _4790_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4791_field = _4169___mcc_h49;
          DAST._IExpression _4792_on = _4168___mcc_h48;
          {
            if (_4789_isDatatype) {
              RAST._IExpr _4793_onExpr;
              DCOMP._IOwnership _4794_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4795_recIdents;
              RAST._IExpr _out1890;
              DCOMP._IOwnership _out1891;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1892;
              (this).GenExpr(_4792_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1890, out _out1891, out _out1892);
              _4793_onExpr = _out1890;
              _4794_onOwned = _out1891;
              _4795_recIdents = _out1892;
              r = ((_4793_onExpr).Sel(DCOMP.__default.escapeName(_4791_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4796_typ;
              RAST._IType _out1893;
              _out1893 = (this).GenType(_4788_fieldType, false, false);
              _4796_typ = _out1893;
              if (((_4796_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1894;
                DCOMP._IOwnership _out1895;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1894, out _out1895);
                r = _out1894;
                resultingOwnership = _out1895;
              }
              readIdents = _4795_recIdents;
            } else {
              RAST._IExpr _4797_onExpr;
              DCOMP._IOwnership _4798_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4799_recIdents;
              RAST._IExpr _out1896;
              DCOMP._IOwnership _out1897;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1898;
              (this).GenExpr(_4792_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1896, out _out1897, out _out1898);
              _4797_onExpr = _out1896;
              _4798_onOwned = _out1897;
              _4799_recIdents = _out1898;
              r = _4797_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4791_field));
              if (_4790_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4800_s;
                _4800_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4797_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4791_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4800_s);
              }
              DCOMP._IOwnership _4801_fromOwnership;
              _4801_fromOwnership = ((_4790_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1899;
              DCOMP._IOwnership _out1900;
              DCOMP.COMP.FromOwnership(r, _4801_fromOwnership, expectedOwnership, out _out1899, out _out1900);
              r = _out1899;
              resultingOwnership = _out1900;
              readIdents = _4799_recIdents;
            }
            return ;
          }
        } else if (_source178.is_SeqBoundedPool) {
          DAST._IExpression _4802___mcc_h231 = _source178.dtor_of;
          bool _4803___mcc_h232 = _source178.dtor_includeDuplicates;
          DAST._IType _4804_fieldType = _4172___mcc_h52;
          bool _4805_isDatatype = _4171___mcc_h51;
          bool _4806_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4807_field = _4169___mcc_h49;
          DAST._IExpression _4808_on = _4168___mcc_h48;
          {
            if (_4805_isDatatype) {
              RAST._IExpr _4809_onExpr;
              DCOMP._IOwnership _4810_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4811_recIdents;
              RAST._IExpr _out1901;
              DCOMP._IOwnership _out1902;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1903;
              (this).GenExpr(_4808_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1901, out _out1902, out _out1903);
              _4809_onExpr = _out1901;
              _4810_onOwned = _out1902;
              _4811_recIdents = _out1903;
              r = ((_4809_onExpr).Sel(DCOMP.__default.escapeName(_4807_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4812_typ;
              RAST._IType _out1904;
              _out1904 = (this).GenType(_4804_fieldType, false, false);
              _4812_typ = _out1904;
              if (((_4812_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1905;
                DCOMP._IOwnership _out1906;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1905, out _out1906);
                r = _out1905;
                resultingOwnership = _out1906;
              }
              readIdents = _4811_recIdents;
            } else {
              RAST._IExpr _4813_onExpr;
              DCOMP._IOwnership _4814_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4815_recIdents;
              RAST._IExpr _out1907;
              DCOMP._IOwnership _out1908;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1909;
              (this).GenExpr(_4808_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1907, out _out1908, out _out1909);
              _4813_onExpr = _out1907;
              _4814_onOwned = _out1908;
              _4815_recIdents = _out1909;
              r = _4813_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4807_field));
              if (_4806_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4816_s;
                _4816_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4813_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4807_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4816_s);
              }
              DCOMP._IOwnership _4817_fromOwnership;
              _4817_fromOwnership = ((_4806_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1910;
              DCOMP._IOwnership _out1911;
              DCOMP.COMP.FromOwnership(r, _4817_fromOwnership, expectedOwnership, out _out1910, out _out1911);
              r = _out1910;
              resultingOwnership = _out1911;
              readIdents = _4815_recIdents;
            }
            return ;
          }
        } else {
          DAST._IExpression _4818___mcc_h235 = _source178.dtor_lo;
          DAST._IExpression _4819___mcc_h236 = _source178.dtor_hi;
          DAST._IType _4820_fieldType = _4172___mcc_h52;
          bool _4821_isDatatype = _4171___mcc_h51;
          bool _4822_isConstant = _4170___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4823_field = _4169___mcc_h49;
          DAST._IExpression _4824_on = _4168___mcc_h48;
          {
            if (_4821_isDatatype) {
              RAST._IExpr _4825_onExpr;
              DCOMP._IOwnership _4826_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4827_recIdents;
              RAST._IExpr _out1912;
              DCOMP._IOwnership _out1913;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1914;
              (this).GenExpr(_4824_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1912, out _out1913, out _out1914);
              _4825_onExpr = _out1912;
              _4826_onOwned = _out1913;
              _4827_recIdents = _out1914;
              r = ((_4825_onExpr).Sel(DCOMP.__default.escapeName(_4823_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4828_typ;
              RAST._IType _out1915;
              _out1915 = (this).GenType(_4820_fieldType, false, false);
              _4828_typ = _out1915;
              if (((_4828_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1916;
                DCOMP._IOwnership _out1917;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1916, out _out1917);
                r = _out1916;
                resultingOwnership = _out1917;
              }
              readIdents = _4827_recIdents;
            } else {
              RAST._IExpr _4829_onExpr;
              DCOMP._IOwnership _4830_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4831_recIdents;
              RAST._IExpr _out1918;
              DCOMP._IOwnership _out1919;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1920;
              (this).GenExpr(_4824_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1918, out _out1919, out _out1920);
              _4829_onExpr = _out1918;
              _4830_onOwned = _out1919;
              _4831_recIdents = _out1920;
              r = _4829_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4823_field));
              if (_4822_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4832_s;
                _4832_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4829_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4823_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4832_s);
              }
              DCOMP._IOwnership _4833_fromOwnership;
              _4833_fromOwnership = ((_4822_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1921;
              DCOMP._IOwnership _out1922;
              DCOMP.COMP.FromOwnership(r, _4833_fromOwnership, expectedOwnership, out _out1921, out _out1922);
              r = _out1921;
              resultingOwnership = _out1922;
              readIdents = _4831_recIdents;
            }
            return ;
          }
        }
      } else if (_source175.is_SelectFn) {
        DAST._IExpression _4834___mcc_h239 = _source175.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _4835___mcc_h240 = _source175.dtor_field;
        bool _4836___mcc_h241 = _source175.dtor_onDatatype;
        bool _4837___mcc_h242 = _source175.dtor_isStatic;
        BigInteger _4838___mcc_h243 = _source175.dtor_arity;
        BigInteger _4839_arity = _4838___mcc_h243;
        bool _4840_isStatic = _4837___mcc_h242;
        bool _4841_isDatatype = _4836___mcc_h241;
        Dafny.ISequence<Dafny.Rune> _4842_field = _4835___mcc_h240;
        DAST._IExpression _4843_on = _4834___mcc_h239;
        {
          RAST._IExpr _4844_onExpr;
          DCOMP._IOwnership _4845_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4846_recIdents;
          RAST._IExpr _out1923;
          DCOMP._IOwnership _out1924;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1925;
          (this).GenExpr(_4843_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1923, out _out1924, out _out1925);
          _4844_onExpr = _out1923;
          _4845_onOwned = _out1924;
          _4846_recIdents = _out1925;
          Dafny.ISequence<Dafny.Rune> _4847_s = Dafny.Sequence<Dafny.Rune>.Empty;
          Dafny.ISequence<Dafny.Rune> _4848_onString;
          _4848_onString = (_4844_onExpr)._ToString(DCOMP.__default.IND);
          if (_4840_isStatic) {
            _4847_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4848_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_4842_field));
          } else {
            _4847_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
            _4847_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4847_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _4848_onString), ((object.Equals(_4845_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            Dafny.ISequence<Dafny.Rune> _4849_args;
            _4849_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            BigInteger _4850_i;
            _4850_i = BigInteger.Zero;
            while ((_4850_i) < (_4839_arity)) {
              if ((_4850_i).Sign == 1) {
                _4849_args = Dafny.Sequence<Dafny.Rune>.Concat(_4849_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _4849_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4849_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_4850_i));
              _4850_i = (_4850_i) + (BigInteger.One);
            }
            _4847_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4847_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _4849_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
            _4847_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4847_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_4842_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _4849_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
            _4847_s = Dafny.Sequence<Dafny.Rune>.Concat(_4847_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            _4847_s = Dafny.Sequence<Dafny.Rune>.Concat(_4847_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
          }
          Dafny.ISequence<Dafny.Rune> _4851_typeShape;
          _4851_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
          BigInteger _4852_i;
          _4852_i = BigInteger.Zero;
          while ((_4852_i) < (_4839_arity)) {
            if ((_4852_i).Sign == 1) {
              _4851_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_4851_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            _4851_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_4851_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
            _4852_i = (_4852_i) + (BigInteger.One);
          }
          _4851_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_4851_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
          _4847_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _4847_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _4851_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          r = RAST.Expr.create_RawExpr(_4847_s);
          RAST._IExpr _out1926;
          DCOMP._IOwnership _out1927;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1926, out _out1927);
          r = _out1926;
          resultingOwnership = _out1927;
          readIdents = _4846_recIdents;
          return ;
        }
      } else if (_source175.is_Index) {
        DAST._IExpression _4853___mcc_h244 = _source175.dtor_expr;
        DAST._ICollKind _4854___mcc_h245 = _source175.dtor_collKind;
        Dafny.ISequence<DAST._IExpression> _4855___mcc_h246 = _source175.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _4856_indices = _4855___mcc_h246;
        DAST._ICollKind _4857_collKind = _4854___mcc_h245;
        DAST._IExpression _4858_on = _4853___mcc_h244;
        {
          RAST._IExpr _4859_onExpr;
          DCOMP._IOwnership _4860_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4861_recIdents;
          RAST._IExpr _out1928;
          DCOMP._IOwnership _out1929;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1930;
          (this).GenExpr(_4858_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1928, out _out1929, out _out1930);
          _4859_onExpr = _out1928;
          _4860_onOwned = _out1929;
          _4861_recIdents = _out1930;
          readIdents = _4861_recIdents;
          r = _4859_onExpr;
          BigInteger _4862_i;
          _4862_i = BigInteger.Zero;
          while ((_4862_i) < (new BigInteger((_4856_indices).Count))) {
            if (object.Equals(_4857_collKind, DAST.CollKind.create_Array())) {
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IExpr _4863_idx;
            DCOMP._IOwnership _4864_idxOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4865_recIdentsIdx;
            RAST._IExpr _out1931;
            DCOMP._IOwnership _out1932;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1933;
            (this).GenExpr((_4856_indices).Select(_4862_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1931, out _out1932, out _out1933);
            _4863_idx = _out1931;
            _4864_idxOwned = _out1932;
            _4865_recIdentsIdx = _out1933;
            r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_4863_idx);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4865_recIdentsIdx);
            _4862_i = (_4862_i) + (BigInteger.One);
          }
          RAST._IExpr _out1934;
          DCOMP._IOwnership _out1935;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1934, out _out1935);
          r = _out1934;
          resultingOwnership = _out1935;
          return ;
        }
      } else if (_source175.is_IndexRange) {
        DAST._IExpression _4866___mcc_h247 = _source175.dtor_expr;
        bool _4867___mcc_h248 = _source175.dtor_isArray;
        Std.Wrappers._IOption<DAST._IExpression> _4868___mcc_h249 = _source175.dtor_low;
        Std.Wrappers._IOption<DAST._IExpression> _4869___mcc_h250 = _source175.dtor_high;
        Std.Wrappers._IOption<DAST._IExpression> _4870_high = _4869___mcc_h250;
        Std.Wrappers._IOption<DAST._IExpression> _4871_low = _4868___mcc_h249;
        bool _4872_isArray = _4867___mcc_h248;
        DAST._IExpression _4873_on = _4866___mcc_h247;
        {
          RAST._IExpr _4874_onExpr;
          DCOMP._IOwnership _4875_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4876_recIdents;
          RAST._IExpr _out1936;
          DCOMP._IOwnership _out1937;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1938;
          (this).GenExpr(_4873_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1936, out _out1937, out _out1938);
          _4874_onExpr = _out1936;
          _4875_onOwned = _out1937;
          _4876_recIdents = _out1938;
          readIdents = _4876_recIdents;
          Dafny.ISequence<Dafny.Rune> _4877_methodName;
          _4877_methodName = (((_4871_low).is_Some) ? ((((_4870_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_4870_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
          Dafny.ISequence<RAST._IExpr> _4878_arguments;
          _4878_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          Std.Wrappers._IOption<DAST._IExpression> _source179 = _4871_low;
          if (_source179.is_None) {
          } else {
            DAST._IExpression _4879___mcc_h280 = _source179.dtor_value;
            DAST._IExpression _4880_l = _4879___mcc_h280;
            {
              RAST._IExpr _4881_lExpr;
              DCOMP._IOwnership _4882___v142;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4883_recIdentsL;
              RAST._IExpr _out1939;
              DCOMP._IOwnership _out1940;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1941;
              (this).GenExpr(_4880_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1939, out _out1940, out _out1941);
              _4881_lExpr = _out1939;
              _4882___v142 = _out1940;
              _4883_recIdentsL = _out1941;
              _4878_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_4878_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_4881_lExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4883_recIdentsL);
            }
          }
          Std.Wrappers._IOption<DAST._IExpression> _source180 = _4870_high;
          if (_source180.is_None) {
          } else {
            DAST._IExpression _4884___mcc_h281 = _source180.dtor_value;
            DAST._IExpression _4885_h = _4884___mcc_h281;
            {
              RAST._IExpr _4886_hExpr;
              DCOMP._IOwnership _4887___v143;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4888_recIdentsH;
              RAST._IExpr _out1942;
              DCOMP._IOwnership _out1943;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1944;
              (this).GenExpr(_4885_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1942, out _out1943, out _out1944);
              _4886_hExpr = _out1942;
              _4887___v143 = _out1943;
              _4888_recIdentsH = _out1944;
              _4878_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_4878_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_4886_hExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4888_recIdentsH);
            }
          }
          r = _4874_onExpr;
          if (_4872_isArray) {
            if (!(_4877_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
              _4877_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _4877_methodName);
            }
            r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _4877_methodName))).Apply(_4878_arguments);
          } else {
            if (!(_4877_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
              r = ((r).Sel(_4877_methodName)).Apply(_4878_arguments);
            }
          }
          RAST._IExpr _out1945;
          DCOMP._IOwnership _out1946;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1945, out _out1946);
          r = _out1945;
          resultingOwnership = _out1946;
          return ;
        }
      } else if (_source175.is_TupleSelect) {
        DAST._IExpression _4889___mcc_h251 = _source175.dtor_expr;
        BigInteger _4890___mcc_h252 = _source175.dtor_index;
        DAST._IType _4891___mcc_h253 = _source175.dtor_fieldType;
        DAST._IType _4892_fieldType = _4891___mcc_h253;
        BigInteger _4893_idx = _4890___mcc_h252;
        DAST._IExpression _4894_on = _4889___mcc_h251;
        {
          RAST._IExpr _4895_onExpr;
          DCOMP._IOwnership _4896_onOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4897_recIdents;
          RAST._IExpr _out1947;
          DCOMP._IOwnership _out1948;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1949;
          (this).GenExpr(_4894_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1947, out _out1948, out _out1949);
          _4895_onExpr = _out1947;
          _4896_onOwnership = _out1948;
          _4897_recIdents = _out1949;
          r = (_4895_onExpr).Sel(Std.Strings.__default.OfNat(_4893_idx));
          RAST._IExpr _out1950;
          DCOMP._IOwnership _out1951;
          DCOMP.COMP.FromOwnership(r, _4896_onOwnership, expectedOwnership, out _out1950, out _out1951);
          r = _out1950;
          resultingOwnership = _out1951;
          readIdents = _4897_recIdents;
          return ;
        }
      } else if (_source175.is_Call) {
        DAST._IExpression _4898___mcc_h254 = _source175.dtor_on;
        DAST._ICallName _4899___mcc_h255 = _source175.dtor_callName;
        Dafny.ISequence<DAST._IType> _4900___mcc_h256 = _source175.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _4901___mcc_h257 = _source175.dtor_args;
        Dafny.ISequence<DAST._IExpression> _4902_args = _4901___mcc_h257;
        Dafny.ISequence<DAST._IType> _4903_typeArgs = _4900___mcc_h256;
        DAST._ICallName _4904_name = _4899___mcc_h255;
        DAST._IExpression _4905_on = _4898___mcc_h254;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          RAST._IExpr _4906_onExpr;
          DCOMP._IOwnership _4907___v144;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4908_recIdents;
          RAST._IExpr _out1952;
          DCOMP._IOwnership _out1953;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1954;
          (this).GenExpr(_4905_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1952, out _out1953, out _out1954);
          _4906_onExpr = _out1952;
          _4907___v144 = _out1953;
          _4908_recIdents = _out1954;
          Dafny.ISequence<RAST._IType> _4909_typeExprs;
          _4909_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
          if ((new BigInteger((_4903_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _hi35 = new BigInteger((_4903_typeArgs).Count);
            for (BigInteger _4910_typeI = BigInteger.Zero; _4910_typeI < _hi35; _4910_typeI++) {
              RAST._IType _4911_typeExpr;
              RAST._IType _out1955;
              _out1955 = (this).GenType((_4903_typeArgs).Select(_4910_typeI), false, false);
              _4911_typeExpr = _out1955;
              _4909_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_4909_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_4911_typeExpr));
            }
          }
          Dafny.ISequence<RAST._IExpr> _4912_argExprs;
          _4912_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi36 = new BigInteger((_4902_args).Count);
          for (BigInteger _4913_i = BigInteger.Zero; _4913_i < _hi36; _4913_i++) {
            DCOMP._IOwnership _4914_argOwnership;
            _4914_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            if (((_4904_name).is_CallName) && ((_4913_i) < (new BigInteger((((_4904_name).dtor_signature)).Count)))) {
              RAST._IType _4915_tpe;
              RAST._IType _out1956;
              _out1956 = (this).GenType(((((_4904_name).dtor_signature)).Select(_4913_i)).dtor_typ, false, false);
              _4915_tpe = _out1956;
              if ((_4915_tpe).CanReadWithoutClone()) {
                _4914_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
              }
            }
            RAST._IExpr _4916_argExpr;
            DCOMP._IOwnership _4917___v145;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4918_argIdents;
            RAST._IExpr _out1957;
            DCOMP._IOwnership _out1958;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1959;
            (this).GenExpr((_4902_args).Select(_4913_i), selfIdent, env, _4914_argOwnership, out _out1957, out _out1958, out _out1959);
            _4916_argExpr = _out1957;
            _4917___v145 = _out1958;
            _4918_argIdents = _out1959;
            _4912_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_4912_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_4916_argExpr));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4918_argIdents);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4908_recIdents);
          Dafny.ISequence<Dafny.Rune> _4919_renderedName;
          _4919_renderedName = ((System.Func<DAST._ICallName, Dafny.ISequence<Dafny.Rune>>)((_source181) => {
            if (_source181.is_CallName) {
              Dafny.ISequence<Dafny.Rune> _4920___mcc_h282 = _source181.dtor_name;
              Std.Wrappers._IOption<DAST._IType> _4921___mcc_h283 = _source181.dtor_onType;
              Dafny.ISequence<DAST._IFormal> _4922___mcc_h284 = _source181.dtor_signature;
              Dafny.ISequence<Dafny.Rune> _4923_ident = _4920___mcc_h282;
              return DCOMP.__default.escapeName(_4923_ident);
            } else if (_source181.is_MapBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else if (_source181.is_MapBuilderBuild) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            } else if (_source181.is_SetBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            }
          }))(_4904_name);
          DAST._IExpression _source182 = _4905_on;
          if (_source182.is_Literal) {
            DAST._ILiteral _4924___mcc_h285 = _source182.dtor_Literal_i_a0;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _4925___mcc_h287 = _source182.dtor_Ident_i_a0;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4926___mcc_h289 = _source182.dtor_Companion_i_a0;
            {
              _4906_onExpr = (_4906_onExpr).MSel(_4919_renderedName);
            }
          } else if (_source182.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _4927___mcc_h291 = _source182.dtor_Tuple_i_a0;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4928___mcc_h293 = _source182.dtor_path;
            Dafny.ISequence<DAST._IType> _4929___mcc_h294 = _source182.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _4930___mcc_h295 = _source182.dtor_args;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _4931___mcc_h299 = _source182.dtor_dims;
            DAST._IType _4932___mcc_h300 = _source182.dtor_typ;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_DatatypeValue) {
            DAST._IDatatypeType _4933___mcc_h303 = _source182.dtor_datatypeType;
            Dafny.ISequence<DAST._IType> _4934___mcc_h304 = _source182.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _4935___mcc_h305 = _source182.dtor_variant;
            bool _4936___mcc_h306 = _source182.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _4937___mcc_h307 = _source182.dtor_contents;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_Convert) {
            DAST._IExpression _4938___mcc_h313 = _source182.dtor_value;
            DAST._IType _4939___mcc_h314 = _source182.dtor_from;
            DAST._IType _4940___mcc_h315 = _source182.dtor_typ;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_SeqConstruct) {
            DAST._IExpression _4941___mcc_h319 = _source182.dtor_length;
            DAST._IExpression _4942___mcc_h320 = _source182.dtor_elem;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _4943___mcc_h323 = _source182.dtor_elements;
            DAST._IType _4944___mcc_h324 = _source182.dtor_typ;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _4945___mcc_h327 = _source182.dtor_elements;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_MultisetValue) {
            Dafny.ISequence<DAST._IExpression> _4946___mcc_h329 = _source182.dtor_elements;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_MapValue) {
            Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _4947___mcc_h331 = _source182.dtor_mapElems;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_MapBuilder) {
            DAST._IType _4948___mcc_h333 = _source182.dtor_keyType;
            DAST._IType _4949___mcc_h334 = _source182.dtor_valueType;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_SeqUpdate) {
            DAST._IExpression _4950___mcc_h337 = _source182.dtor_expr;
            DAST._IExpression _4951___mcc_h338 = _source182.dtor_indexExpr;
            DAST._IExpression _4952___mcc_h339 = _source182.dtor_value;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_MapUpdate) {
            DAST._IExpression _4953___mcc_h343 = _source182.dtor_expr;
            DAST._IExpression _4954___mcc_h344 = _source182.dtor_indexExpr;
            DAST._IExpression _4955___mcc_h345 = _source182.dtor_value;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_SetBuilder) {
            DAST._IType _4956___mcc_h349 = _source182.dtor_elemType;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_ToMultiset) {
            DAST._IExpression _4957___mcc_h351 = _source182.dtor_ToMultiset_i_a0;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_This) {
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_Ite) {
            DAST._IExpression _4958___mcc_h353 = _source182.dtor_cond;
            DAST._IExpression _4959___mcc_h354 = _source182.dtor_thn;
            DAST._IExpression _4960___mcc_h355 = _source182.dtor_els;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_UnOp) {
            DAST._IUnaryOp _4961___mcc_h359 = _source182.dtor_unOp;
            DAST._IExpression _4962___mcc_h360 = _source182.dtor_expr;
            DAST.Format._IUnaryOpFormat _4963___mcc_h361 = _source182.dtor_format1;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_BinOp) {
            DAST._IBinOp _4964___mcc_h365 = _source182.dtor_op;
            DAST._IExpression _4965___mcc_h366 = _source182.dtor_left;
            DAST._IExpression _4966___mcc_h367 = _source182.dtor_right;
            DAST.Format._IBinaryOpFormat _4967___mcc_h368 = _source182.dtor_format2;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_ArrayLen) {
            DAST._IExpression _4968___mcc_h373 = _source182.dtor_expr;
            BigInteger _4969___mcc_h374 = _source182.dtor_dim;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_MapKeys) {
            DAST._IExpression _4970___mcc_h377 = _source182.dtor_expr;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_MapValues) {
            DAST._IExpression _4971___mcc_h379 = _source182.dtor_expr;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_Select) {
            DAST._IExpression _4972___mcc_h381 = _source182.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _4973___mcc_h382 = _source182.dtor_field;
            bool _4974___mcc_h383 = _source182.dtor_isConstant;
            bool _4975___mcc_h384 = _source182.dtor_onDatatype;
            DAST._IType _4976___mcc_h385 = _source182.dtor_fieldType;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_SelectFn) {
            DAST._IExpression _4977___mcc_h391 = _source182.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _4978___mcc_h392 = _source182.dtor_field;
            bool _4979___mcc_h393 = _source182.dtor_onDatatype;
            bool _4980___mcc_h394 = _source182.dtor_isStatic;
            BigInteger _4981___mcc_h395 = _source182.dtor_arity;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_Index) {
            DAST._IExpression _4982___mcc_h401 = _source182.dtor_expr;
            DAST._ICollKind _4983___mcc_h402 = _source182.dtor_collKind;
            Dafny.ISequence<DAST._IExpression> _4984___mcc_h403 = _source182.dtor_indices;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_IndexRange) {
            DAST._IExpression _4985___mcc_h407 = _source182.dtor_expr;
            bool _4986___mcc_h408 = _source182.dtor_isArray;
            Std.Wrappers._IOption<DAST._IExpression> _4987___mcc_h409 = _source182.dtor_low;
            Std.Wrappers._IOption<DAST._IExpression> _4988___mcc_h410 = _source182.dtor_high;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_TupleSelect) {
            DAST._IExpression _4989___mcc_h415 = _source182.dtor_expr;
            BigInteger _4990___mcc_h416 = _source182.dtor_index;
            DAST._IType _4991___mcc_h417 = _source182.dtor_fieldType;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_Call) {
            DAST._IExpression _4992___mcc_h421 = _source182.dtor_on;
            DAST._ICallName _4993___mcc_h422 = _source182.dtor_callName;
            Dafny.ISequence<DAST._IType> _4994___mcc_h423 = _source182.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _4995___mcc_h424 = _source182.dtor_args;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _4996___mcc_h429 = _source182.dtor_params;
            DAST._IType _4997___mcc_h430 = _source182.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _4998___mcc_h431 = _source182.dtor_body;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _4999___mcc_h435 = _source182.dtor_values;
            DAST._IType _5000___mcc_h436 = _source182.dtor_retType;
            DAST._IExpression _5001___mcc_h437 = _source182.dtor_expr;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _5002___mcc_h441 = _source182.dtor_name;
            DAST._IType _5003___mcc_h442 = _source182.dtor_typ;
            DAST._IExpression _5004___mcc_h443 = _source182.dtor_value;
            DAST._IExpression _5005___mcc_h444 = _source182.dtor_iifeBody;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_Apply) {
            DAST._IExpression _5006___mcc_h449 = _source182.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _5007___mcc_h450 = _source182.dtor_args;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_TypeTest) {
            DAST._IExpression _5008___mcc_h453 = _source182.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _5009___mcc_h454 = _source182.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _5010___mcc_h455 = _source182.dtor_variant;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_InitializationValue) {
            DAST._IType _5011___mcc_h459 = _source182.dtor_typ;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_BoolBoundedPool) {
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_SetBoundedPool) {
            DAST._IExpression _5012___mcc_h461 = _source182.dtor_of;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else if (_source182.is_SeqBoundedPool) {
            DAST._IExpression _5013___mcc_h463 = _source182.dtor_of;
            bool _5014___mcc_h464 = _source182.dtor_includeDuplicates;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          } else {
            DAST._IExpression _5015___mcc_h467 = _source182.dtor_lo;
            DAST._IExpression _5016___mcc_h468 = _source182.dtor_hi;
            {
              _4906_onExpr = (_4906_onExpr).Sel(_4919_renderedName);
            }
          }
          r = _4906_onExpr;
          if ((new BigInteger((_4909_typeExprs).Count)).Sign == 1) {
            r = (r).ApplyType(_4909_typeExprs);
          }
          r = (r).Apply(_4912_argExprs);
          RAST._IExpr _out1960;
          DCOMP._IOwnership _out1961;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1960, out _out1961);
          r = _out1960;
          resultingOwnership = _out1961;
          return ;
        }
      } else if (_source175.is_Lambda) {
        Dafny.ISequence<DAST._IFormal> _5017___mcc_h258 = _source175.dtor_params;
        DAST._IType _5018___mcc_h259 = _source175.dtor_retType;
        Dafny.ISequence<DAST._IStatement> _5019___mcc_h260 = _source175.dtor_body;
        Dafny.ISequence<DAST._IStatement> _5020_body = _5019___mcc_h260;
        DAST._IType _5021_retType = _5018___mcc_h259;
        Dafny.ISequence<DAST._IFormal> _5022_paramsDafny = _5017___mcc_h258;
        {
          Dafny.ISequence<RAST._IFormal> _5023_params;
          Dafny.ISequence<RAST._IFormal> _out1962;
          _out1962 = (this).GenParams(_5022_paramsDafny);
          _5023_params = _out1962;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _5024_paramNames;
          _5024_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _5025_paramTypesMap;
          _5025_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
          BigInteger _hi37 = new BigInteger((_5023_params).Count);
          for (BigInteger _5026_i = BigInteger.Zero; _5026_i < _hi37; _5026_i++) {
            Dafny.ISequence<Dafny.Rune> _5027_name;
            _5027_name = ((_5023_params).Select(_5026_i)).dtor_name;
            _5024_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_5024_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_5027_name));
            _5025_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_5025_paramTypesMap, _5027_name, ((_5023_params).Select(_5026_i)).dtor_tpe);
          }
          DCOMP._IEnvironment _5028_env;
          _5028_env = DCOMP.Environment.create(_5024_paramNames, _5025_paramTypesMap);
          RAST._IExpr _5029_recursiveGen;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5030_recIdents;
          DCOMP._IEnvironment _5031___v150;
          RAST._IExpr _out1963;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1964;
          DCOMP._IEnvironment _out1965;
          (this).GenStmts(_5020_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), _5028_env, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out1963, out _out1964, out _out1965);
          _5029_recursiveGen = _out1963;
          _5030_recIdents = _out1964;
          _5031___v150 = _out1965;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          _5030_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_5030_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_5032_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
            var _coll6 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
            foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in (_5032_paramNames).CloneAsArray()) {
              Dafny.ISequence<Dafny.Rune> _5033_name = (Dafny.ISequence<Dafny.Rune>)_compr_6;
              if ((_5032_paramNames).Contains(_5033_name)) {
                _coll6.Add(_5033_name);
              }
            }
            return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll6);
          }))())(_5024_paramNames));
          RAST._IExpr _5034_allReadCloned;
          _5034_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          while (!(_5030_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
            Dafny.ISequence<Dafny.Rune> _5035_next;
            foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_5030_recIdents).Elements) {
              _5035_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
              if ((_5030_recIdents).Contains(_5035_next)) {
                goto after__ASSIGN_SUCH_THAT_3;
              }
            }
            throw new System.Exception("assign-such-that search produced no value (line 3726)");
          after__ASSIGN_SUCH_THAT_3: ;
            if ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) && ((_5035_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
              if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
                _5034_allReadCloned = (_5034_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
              }
            } else if (!((_5024_paramNames).Contains(_5035_next))) {
              _5034_allReadCloned = (_5034_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _5035_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.Expr.create_Identifier(_5035_next)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_5035_next));
            }
            _5030_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_5030_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_5035_next));
          }
          RAST._IType _5036_retTypeGen;
          RAST._IType _out1966;
          _out1966 = (this).GenType(_5021_retType, false, true);
          _5036_retTypeGen = _out1966;
          r = RAST.Expr.create_Block((_5034_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_5023_params, Std.Wrappers.Option<RAST._IType>.create_Some(_5036_retTypeGen), RAST.Expr.create_Block(_5029_recursiveGen)))));
          RAST._IExpr _out1967;
          DCOMP._IOwnership _out1968;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1967, out _out1968);
          r = _out1967;
          resultingOwnership = _out1968;
          return ;
        }
      } else if (_source175.is_BetaRedex) {
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _5037___mcc_h261 = _source175.dtor_values;
        DAST._IType _5038___mcc_h262 = _source175.dtor_retType;
        DAST._IExpression _5039___mcc_h263 = _source175.dtor_expr;
        DAST._IExpression _5040_expr = _5039___mcc_h263;
        DAST._IType _5041_retType = _5038___mcc_h262;
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _5042_values = _5037___mcc_h261;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _5043_paramNames;
          _5043_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<RAST._IFormal> _5044_paramFormals;
          Dafny.ISequence<RAST._IFormal> _out1969;
          _out1969 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_5045_value) => {
            return (_5045_value).dtor__0;
          })), _5042_values));
          _5044_paramFormals = _out1969;
          Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _5046_paramTypes;
          _5046_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5047_paramNamesSet;
          _5047_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _hi38 = new BigInteger((_5042_values).Count);
          for (BigInteger _5048_i = BigInteger.Zero; _5048_i < _hi38; _5048_i++) {
            Dafny.ISequence<Dafny.Rune> _5049_name;
            _5049_name = (((_5042_values).Select(_5048_i)).dtor__0).dtor_name;
            Dafny.ISequence<Dafny.Rune> _5050_rName;
            _5050_rName = DCOMP.__default.escapeName(_5049_name);
            _5043_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_5043_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_5050_rName));
            _5046_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_5046_paramTypes, _5050_rName, ((_5044_paramFormals).Select(_5048_i)).dtor_tpe);
            _5047_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_5047_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_5050_rName));
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          BigInteger _hi39 = new BigInteger((_5042_values).Count);
          for (BigInteger _5051_i = BigInteger.Zero; _5051_i < _hi39; _5051_i++) {
            RAST._IType _5052_typeGen;
            RAST._IType _out1970;
            _out1970 = (this).GenType((((_5042_values).Select(_5051_i)).dtor__0).dtor_typ, false, true);
            _5052_typeGen = _out1970;
            RAST._IExpr _5053_valueGen;
            DCOMP._IOwnership _5054___v151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5055_recIdents;
            RAST._IExpr _out1971;
            DCOMP._IOwnership _out1972;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1973;
            (this).GenExpr(((_5042_values).Select(_5051_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1971, out _out1972, out _out1973);
            _5053_valueGen = _out1971;
            _5054___v151 = _out1972;
            _5055_recIdents = _out1973;
            r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_5042_values).Select(_5051_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_5052_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_5053_valueGen)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _5055_recIdents);
          }
          DCOMP._IEnvironment _5056_newEnv;
          _5056_newEnv = DCOMP.Environment.create(_5043_paramNames, _5046_paramTypes);
          RAST._IExpr _5057_recGen;
          DCOMP._IOwnership _5058_recOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5059_recIdents;
          RAST._IExpr _out1974;
          DCOMP._IOwnership _out1975;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1976;
          (this).GenExpr(_5040_expr, selfIdent, _5056_newEnv, expectedOwnership, out _out1974, out _out1975, out _out1976);
          _5057_recGen = _out1974;
          _5058_recOwned = _out1975;
          _5059_recIdents = _out1976;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_5059_recIdents, _5047_paramNamesSet);
          r = RAST.Expr.create_Block((r).Then(_5057_recGen));
          RAST._IExpr _out1977;
          DCOMP._IOwnership _out1978;
          DCOMP.COMP.FromOwnership(r, _5058_recOwned, expectedOwnership, out _out1977, out _out1978);
          r = _out1977;
          resultingOwnership = _out1978;
          return ;
        }
      } else if (_source175.is_IIFE) {
        Dafny.ISequence<Dafny.Rune> _5060___mcc_h264 = _source175.dtor_name;
        DAST._IType _5061___mcc_h265 = _source175.dtor_typ;
        DAST._IExpression _5062___mcc_h266 = _source175.dtor_value;
        DAST._IExpression _5063___mcc_h267 = _source175.dtor_iifeBody;
        DAST._IExpression _5064_iifeBody = _5063___mcc_h267;
        DAST._IExpression _5065_value = _5062___mcc_h266;
        DAST._IType _5066_tpe = _5061___mcc_h265;
        Dafny.ISequence<Dafny.Rune> _5067_name = _5060___mcc_h264;
        {
          RAST._IExpr _5068_valueGen;
          DCOMP._IOwnership _5069___v152;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5070_recIdents;
          RAST._IExpr _out1979;
          DCOMP._IOwnership _out1980;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1981;
          (this).GenExpr(_5065_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1979, out _out1980, out _out1981);
          _5068_valueGen = _out1979;
          _5069___v152 = _out1980;
          _5070_recIdents = _out1981;
          readIdents = _5070_recIdents;
          RAST._IType _5071_valueTypeGen;
          RAST._IType _out1982;
          _out1982 = (this).GenType(_5066_tpe, false, true);
          _5071_valueTypeGen = _out1982;
          RAST._IExpr _5072_bodyGen;
          DCOMP._IOwnership _5073___v153;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5074_bodyIdents;
          RAST._IExpr _out1983;
          DCOMP._IOwnership _out1984;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1985;
          (this).GenExpr(_5064_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1983, out _out1984, out _out1985);
          _5072_bodyGen = _out1983;
          _5073___v153 = _out1984;
          _5074_bodyIdents = _out1985;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_5074_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_5067_name)))));
          r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_5067_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_5071_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_5068_valueGen))).Then(_5072_bodyGen));
          RAST._IExpr _out1986;
          DCOMP._IOwnership _out1987;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1986, out _out1987);
          r = _out1986;
          resultingOwnership = _out1987;
          return ;
        }
      } else if (_source175.is_Apply) {
        DAST._IExpression _5075___mcc_h268 = _source175.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _5076___mcc_h269 = _source175.dtor_args;
        Dafny.ISequence<DAST._IExpression> _5077_args = _5076___mcc_h269;
        DAST._IExpression _5078_func = _5075___mcc_h268;
        {
          RAST._IExpr _5079_funcExpr;
          DCOMP._IOwnership _5080___v154;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5081_recIdents;
          RAST._IExpr _out1988;
          DCOMP._IOwnership _out1989;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1990;
          (this).GenExpr(_5078_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1988, out _out1989, out _out1990);
          _5079_funcExpr = _out1988;
          _5080___v154 = _out1989;
          _5081_recIdents = _out1990;
          readIdents = _5081_recIdents;
          Dafny.ISequence<RAST._IExpr> _5082_rArgs;
          _5082_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi40 = new BigInteger((_5077_args).Count);
          for (BigInteger _5083_i = BigInteger.Zero; _5083_i < _hi40; _5083_i++) {
            RAST._IExpr _5084_argExpr;
            DCOMP._IOwnership _5085_argOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5086_argIdents;
            RAST._IExpr _out1991;
            DCOMP._IOwnership _out1992;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1993;
            (this).GenExpr((_5077_args).Select(_5083_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1991, out _out1992, out _out1993);
            _5084_argExpr = _out1991;
            _5085_argOwned = _out1992;
            _5086_argIdents = _out1993;
            _5082_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_5082_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_5084_argExpr));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _5086_argIdents);
          }
          r = (_5079_funcExpr).Apply(_5082_rArgs);
          RAST._IExpr _out1994;
          DCOMP._IOwnership _out1995;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1994, out _out1995);
          r = _out1994;
          resultingOwnership = _out1995;
          return ;
        }
      } else if (_source175.is_TypeTest) {
        DAST._IExpression _5087___mcc_h270 = _source175.dtor_on;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _5088___mcc_h271 = _source175.dtor_dType;
        Dafny.ISequence<Dafny.Rune> _5089___mcc_h272 = _source175.dtor_variant;
        Dafny.ISequence<Dafny.Rune> _5090_variant = _5089___mcc_h272;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _5091_dType = _5088___mcc_h271;
        DAST._IExpression _5092_on = _5087___mcc_h270;
        {
          RAST._IExpr _5093_exprGen;
          DCOMP._IOwnership _5094___v155;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5095_recIdents;
          RAST._IExpr _out1996;
          DCOMP._IOwnership _out1997;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1998;
          (this).GenExpr(_5092_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1996, out _out1997, out _out1998);
          _5093_exprGen = _out1996;
          _5094___v155 = _out1997;
          _5095_recIdents = _out1998;
          RAST._IType _5096_dTypePath;
          RAST._IType _out1999;
          _out1999 = DCOMP.COMP.GenPath(_5091_dType);
          _5096_dTypePath = _out1999;
          r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_5093_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_5096_dTypePath).MSel(DCOMP.__default.escapeName(_5090_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
          RAST._IExpr _out2000;
          DCOMP._IOwnership _out2001;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2000, out _out2001);
          r = _out2000;
          resultingOwnership = _out2001;
          readIdents = _5095_recIdents;
          return ;
        }
      } else if (_source175.is_InitializationValue) {
        DAST._IType _5097___mcc_h273 = _source175.dtor_typ;
        DAST._IType _5098_typ = _5097___mcc_h273;
        {
          RAST._IType _5099_typExpr;
          RAST._IType _out2002;
          _out2002 = (this).GenType(_5098_typ, false, false);
          _5099_typExpr = _out2002;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_5099_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
          RAST._IExpr _out2003;
          DCOMP._IOwnership _out2004;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2003, out _out2004);
          r = _out2003;
          resultingOwnership = _out2004;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source175.is_BoolBoundedPool) {
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
      } else if (_source175.is_SetBoundedPool) {
        DAST._IExpression _5100___mcc_h274 = _source175.dtor_of;
        DAST._IExpression _5101_of = _5100___mcc_h274;
        {
          RAST._IExpr _5102_exprGen;
          DCOMP._IOwnership _5103___v156;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5104_recIdents;
          RAST._IExpr _out2007;
          DCOMP._IOwnership _out2008;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2009;
          (this).GenExpr(_5101_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out2007, out _out2008, out _out2009);
          _5102_exprGen = _out2007;
          _5103___v156 = _out2008;
          _5104_recIdents = _out2009;
          r = ((((_5102_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out2010;
          DCOMP._IOwnership _out2011;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2010, out _out2011);
          r = _out2010;
          resultingOwnership = _out2011;
          readIdents = _5104_recIdents;
          return ;
        }
      } else if (_source175.is_SeqBoundedPool) {
        DAST._IExpression _5105___mcc_h275 = _source175.dtor_of;
        bool _5106___mcc_h276 = _source175.dtor_includeDuplicates;
        bool _5107_includeDuplicates = _5106___mcc_h276;
        DAST._IExpression _5108_of = _5105___mcc_h275;
        {
          RAST._IExpr _5109_exprGen;
          DCOMP._IOwnership _5110___v157;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5111_recIdents;
          RAST._IExpr _out2012;
          DCOMP._IOwnership _out2013;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2014;
          (this).GenExpr(_5108_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out2012, out _out2013, out _out2014);
          _5109_exprGen = _out2012;
          _5110___v157 = _out2013;
          _5111_recIdents = _out2014;
          r = ((_5109_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          if (!(_5107_includeDuplicates)) {
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
          }
          RAST._IExpr _out2015;
          DCOMP._IOwnership _out2016;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2015, out _out2016);
          r = _out2015;
          resultingOwnership = _out2016;
          readIdents = _5111_recIdents;
          return ;
        }
      } else {
        DAST._IExpression _5112___mcc_h277 = _source175.dtor_lo;
        DAST._IExpression _5113___mcc_h278 = _source175.dtor_hi;
        DAST._IExpression _5114_hi = _5113___mcc_h278;
        DAST._IExpression _5115_lo = _5112___mcc_h277;
        {
          RAST._IExpr _5116_lo;
          DCOMP._IOwnership _5117___v158;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5118_recIdentsLo;
          RAST._IExpr _out2017;
          DCOMP._IOwnership _out2018;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2019;
          (this).GenExpr(_5115_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out2017, out _out2018, out _out2019);
          _5116_lo = _out2017;
          _5117___v158 = _out2018;
          _5118_recIdentsLo = _out2019;
          RAST._IExpr _5119_hi;
          DCOMP._IOwnership _5120___v159;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5121_recIdentsHi;
          RAST._IExpr _out2020;
          DCOMP._IOwnership _out2021;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2022;
          (this).GenExpr(_5114_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out2020, out _out2021, out _out2022);
          _5119_hi = _out2020;
          _5120___v159 = _out2021;
          _5121_recIdentsHi = _out2022;
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_5116_lo, _5119_hi));
          RAST._IExpr _out2023;
          DCOMP._IOwnership _out2024;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2023, out _out2024);
          r = _out2023;
          resultingOwnership = _out2024;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_5118_recIdentsLo, _5121_recIdentsHi);
          return ;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      BigInteger _5122_i;
      _5122_i = BigInteger.Zero;
      while ((_5122_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _5123_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _5124_m;
        RAST._IMod _out2025;
        _out2025 = (this).GenModule((p).Select(_5122_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _5124_m = _out2025;
        _5123_generated = (_5124_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_5122_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _5123_generated);
        _5122_i = (_5122_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _5125_i;
      _5125_i = BigInteger.Zero;
      while ((_5125_i) < (new BigInteger((fullName).Count))) {
        if ((_5125_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_5125_i)));
        _5125_i = (_5125_i) + (BigInteger.One);
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